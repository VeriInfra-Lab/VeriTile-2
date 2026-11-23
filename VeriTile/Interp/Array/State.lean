import VeriTile.Interp.State
import VeriTile.Triton.Core.Reshape

namespace VeriTile.Interp.Array

open VeriTile.Triton VeriTile.Triton.FP

/-- Sparse memory packs the written cells into an array. Rewriting an address reuses
its slot. Arbitrarily large offsets and untouched regions consume no array space. -/
structure Memory (α : Type) where
  cells : _root_.Array (Structural.Cell α) := #[]
  slots : Std.HashMap (RegionName × Nat) Nat := {}
  bounded : ∀ {a : RegionName × Nat} {j : Nat}, slots[a]? = some j → j < cells.size := by simp
  unique : ∀ {a b : RegionName × Nat} {j : Nat}, slots[a]? = some j → slots[b]? = some j → a = b := by simp

namespace Memory

variable {α : Type}

def read (m : Memory α) (r : RegionName) (o : Nat) (initial : RegionName → Nat → Structural.Cell α) :
    Structural.Cell α :=
  match h : m.slots[(r, o)]? with
  | some j => m.cells[j]'(m.bounded h)
  | none => initial r o

def write (m : Memory α) (a : RegionName × Nat) (c : Structural.Cell α) : Memory α :=
  match h : m.slots[a]? with
  | some j => { m with
      cells := m.cells.set j c (m.bounded h)
      bounded := by intro _ _ hi; simpa only [Array.size_set] using m.bounded hi }
  | none =>
    { cells := m.cells.push c
      slots := m.slots.insert a m.cells.size
      bounded := by
        intro k j hj
        by_cases hk : k = a
        · subst k; simp at hj; simp [← hj]
        · simp [Std.HashMap.getElem?_insert, Ne.symm hk] at hj
          simpa only [Array.size_push] using Nat.lt_succ_of_lt (m.bounded hj)
      unique := by
        intro k l j hk hl
        by_cases hka : k = a <;> by_cases hla : l = a
        · exact hka.trans hla.symm
        · subst k; simp at hk
          simp [Std.HashMap.getElem?_insert, Ne.symm hla] at hl
          have := m.bounded hl; omega
        · subst l; simp at hl
          simp [Std.HashMap.getElem?_insert, Ne.symm hka] at hk
          have := m.bounded hk; omega
        · apply m.unique (j := j)
          · simpa [Std.HashMap.getElem?_insert, Ne.symm hka] using hk
          · simpa [Std.HashMap.getElem?_insert, Ne.symm hla] using hl
    }

end Memory

/-- Tabulate a register tile once, in the same row-major order as `linearIndex`. -/
def materialize {β : Type} {sh : TileShape} (f : TileIndex sh → β) : TileIndex sh → β :=
  let lanes := (TileShape.allIndices sh).toArray.map f
  fun i => lanes[TileShape.linearIndex sh i]'(by simpa [lanes] using TileShape.linearIndex_lt sh i)

structure State (α : Type) where
  memory : Memory α := {}
  init : RegionName → Nat → Structural.Cell α
  regs : Std.HashMap RegName (Interp.Reg α) := {}
  pids : Nat → Nat
  numPids : Nat → Nat
  undef : (d : TileDType) → RegionName → Nat → Structural.Value α d

namespace State

variable {α : Type}

def read (s : State α) (r : RegionName) (o : Nat) : Structural.Cell α := s.memory.read r o s.init

def write (s : State α) (a : RegionName × Nat) (c : Structural.Cell α) : State α :=
  { s with memory := s.memory.write a c }

def setReg (s : State α) (n : RegName) (d : TileDType) (sh : TileShape)
    (v : Structural.Values α d sh) : State α :=
  { s with regs := s.regs.insert n ⟨d, sh, materialize v⟩ }

/-- The expression evaluator shares materialized registers and reads the array through
its initial-memory callback. Constructing this read view copies no cells or tiles. -/
def view (s : State α) : Interp.State α where
  init := s.read
  regs := s.regs
  pids := s.pids
  numPids := s.numPids
  undef := s.undef

end State
end VeriTile.Interp.Array
