import VeriTile.Dist.Frontend.TritonDist.Shmem

namespace VeriTile.Tests.TritonDistShmem

open Lean
open VeriTile.Dist
open VeriTile.Dist.Frontend.TritonDist
open scoped VeriTile.Dist.Frontend.TritonDist

private def cta : Cta := ⟨0, [3]⟩
private def block : Agent := .cta cta
private def warp : Agent := .group cta 4
private def range (rank : Rank) (region : String) : List Addr :=
  [⟨.global rank, ⟨region⟩, 10⟩, ⟨.global rank, ⟨region⟩, 11⟩]

private def flag (rank : Rank) : Addr := ⟨.global rank, ⟨"flag"⟩, 3⟩

private def ctx : Shmem.Context where
  issuer := block
  peCount := 3
  symmetric := fun _ => Bool.true
  evalNat := fun expr =>
    match expr[0][0].getAtomVal with
    | "2" => some 2
    | "7" => some 7
    | "8" => some 8
    | _ => none
  evalByteRange := fun expr bytes => do
    guard (bytes = 8)
    match expr[0].getId with
    | `dst => some (range 0 "dst")
    | `src => some (range 0 "src")
    | _ => none
  evalSignalWord := fun expr => if expr[0].getId == `signal then some (flag 0) else none
  collectiveReady := fun _ => Bool.true
  teamRound := some ⟨11, 2⟩

private def lower (context : Shmem.Context) (source : Shmem.Source) : Option Shmem.Result := do
  let site ← source.sites.head?
  site.call.lower context

private def plan (context : Shmem.Context) (source : Shmem.Source) : Option Shmem.TransferPlan := do
  let .transfer transfer ← lower context source | none
  pure transfer

private def delivered (issuer : Agent) : Option Bump :=
  some ⟨.delivered issuer, .add, 1, .shmem .release⟩

private def getCopy (nbi : Bool) : Transfer :=
  ⟨range 2 "src", range 0 "dst", nbi, delivered block⟩

private def putCopy (nbi : Bool) (completion : Option Bump := delivered block) : Transfer :=
  ⟨range 0 "src", range 2 "dst", nbi, completion⟩

private def signal (op : SignalOp) : Option Bump :=
  some ⟨.word (flag 2), op, 7, .shmem .release⟩

-- Reduced call shapes from the signed table. Blocking get is exercised by
-- all_to_all_vdev_2d_offset_inter_node.py:299 at TD 7908e4ea; nonblocking get
-- by all_to_all_vdev_2d_offset.py:291.
example :
    (plan ctx (triton { libshmem_device.getmem_block(dst, src, 8, 2) })).map
      Shmem.TransferPlan.callStep =
      some [.initiate (getCopy Bool.false), .complete (getCopy Bool.false)] := rfl

example :
    plan ctx (triton { libshmem_device.getmem_nbi_block(dst, src, 8, 2) }) =
      some ⟨block, getCopy Bool.true, Bool.false⟩ := rfl

private def blockingPut : Shmem.Source :=
  triton { libshmem_device.putmem_block(dst, src, 8, 2) }

example :
    (plan ctx blockingPut).map Shmem.TransferPlan.callStep =
      some [.initiate (putCopy Bool.false)] := rfl

/-- A blocking put reads the local payload and later stores the remote
payload with plain access modes. Its release is the private delivery count. -/
theorem putmemBlockPayloadPlain :
    (plan ctx blockingPut).map (fun p =>
      ((Event.initiate p.transfer).accesses, (Event.complete p.transfer).accesses,
        (Event.complete p.transfer).releaseOf?)) =
      some ((range 0 "src").map (fun p => (.load, p, .plain)),
        (range 2 "dst").map (fun p => (.store, p, .plain)),
        some (.delivered block, .shmem .release)) := rfl

#print axioms putmemBlockPayloadPlain

example :
    plan ctx (triton { libshmem_device.putmem_nbi_block(dst, src, 8, 2) }) =
      some ⟨block, putCopy Bool.true, Bool.false⟩ := rfl

example :
    plan ctx (triton {
      libshmem_device.putmem_signal_block(dst, src, 8, signal, 7,
        libshmem_device.NVSHMEM_SIGNAL_SET, 2)
    }) = some ⟨block, putCopy Bool.false (signal .set), Bool.false⟩ := rfl

example :
    plan ctx (triton {
      libshmem_device.putmem_signal_nbi_block(dst, src, 8, signal, 7,
        libshmem_device.NVSHMEM_SIGNAL_SET, 2)
    }) = some ⟨block, putCopy Bool.true (signal .set), Bool.false⟩ := rfl

-- Reduced byte-pointer view from tutorials/03-inter-node-allgather.py:85
-- at Triton-distributed 7908e4ea. The caller resolves the view and byte count.
example : (triton {
    libshmem_device.putmem_signal_block(
      tl.cast(dst, tl.pointer_type(tl.int8)) + offset,
      tl.cast(src, tl.pointer_type(tl.int8)) + offset,
      size, signal, amount, libshmem_device.NVSHMEM_SIGNAL_SET, pe)
  } : Shmem.Source).sites.length = 1 := rfl

private def warpPut : Shmem.Source :=
  triton {
    libshmem_device.putmem_signal_nbi_warp(dst, src, 8, signal, 7,
      libshmem_device.NVSHMEM_SIGNAL_ADD, 2)
  }

example :
    plan { ctx with issuer := warp } warpPut =
      some ⟨warp, putCopy Bool.true (signal .add), Bool.false⟩ := rfl

example : plan ctx warpPut = none := rfl

example : plan { ctx with collectiveReady := fun _ => Bool.false } blockingPut = none := rfl

example : plan { ctx with symmetric := fun _ => Bool.false } blockingPut = none := rfl

example :
    lower ctx (triton {
      libshmem_device.signal_op(signal, 7, libshmem_device.NVSHMEM_SIGNAL_ADD, 2)
    }) = some (.event (.bump ⟨.word (flag 2), .add, 7, .shmem .release⟩)) := rfl

example :
    lower ctx (triton {
      libshmem_device.signal_wait_until(signal, libshmem_device.NVSHMEM_CMP_EQ, 7)
    }) = some (.event (.wait (.word (flag 0)) .eq 7 (.shmem .acquire))) := rfl

example :
    lower ctx (triton { libshmem_device.fence() }) =
      some (.event (.fence (.shmem .release))) ∧
    (Event.fence (.shmem .release)).releaseOf? = none := ⟨rfl, rfl⟩

private def peBarrier : Shmem.Barrier := ⟨block, ⟨11, 2⟩, 3⟩

example :
    lower ctx (triton { libshmem_device.barrier_all_block() }) =
      some (.barrier peBarrier) := rfl

example : peBarrier.events =
    [.bump ⟨.rendezvous 23, .add, 1, .shmem .release⟩,
      .wait (.rendezvous 23) .ge 6 (.shmem .acquire)] := rfl

-- Tickets 1 and 2 represent distinct earlier transfers, including a
-- signalling put, issued by this block and another warp respectively.
example : peBarrier.ReturnsAfterTransfers [(block, 1), (warp, 2)] (· = 1) := by
  intro occurrence member
  simpa [peBarrier, block, warp] using member

example : ¬ peBarrier.ReturnsAfterTransfers [(block, 1), (warp, 2)] (· = 2) := by
  intro after
  have finished : (1 : Nat) = 2 := after 1 (by simp [peBarrier])
  contradiction

/-- error: unsupported NVSHMEM signal operation 'libshmem_device.NVSHMEM_SIGNAL_XOR' -/
#guard_msgs in
#check (triton {
  libshmem_device.signal_op(signal, 7, libshmem_device.NVSHMEM_SIGNAL_XOR, 2)
} : Shmem.Source)

/-- error: unsupported NVSHMEM signal comparison 'libshmem_device.NVSHMEM_CMP_INVALID' -/
#guard_msgs in
#check (triton {
  libshmem_device.signal_wait_until(signal, libshmem_device.NVSHMEM_CMP_INVALID, 7)
} : Shmem.Source)

/-- error: not implemented: #81 -/
#guard_msgs in
#check (triton {
  libshmem_device.fence()
  __syncthreads()
} : Shmem.Source)

/-- error: random source helper requires an explicit tl.source_helper binding -/
#guard_msgs in
#check (triton {
  libshmem_device.fence()
  x = dl.allocate_smem(1)
} : Shmem.Source)

/-- error: mixed dl and NVSHMEM blocks require the segment frontend (#82) -/
#guard_msgs in
#check (triton {
  libshmem_device.fence()
  r = dl.rank()
} : Shmem.Source)

/-- error: tl.load: unknown kwarg `volatile`. Only `mask`, `other`, `dtype`, `boundary_check`, `padding_option`, and `eviction_policy` are recognized. -/
#guard_msgs in
#check (triton {
  libshmem_device.fence()
  tl.region p = tl.int32
  x = tl.load(p + 0, volatile=True)
} : Shmem.Source)

end VeriTile.Tests.TritonDistShmem
