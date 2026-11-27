#include <tl_templates/cuda/gemm.h>
#include <tl_templates/cuda/copy.h>
#include <tl_templates/cuda/reduce.h>
#include <tl_templates/cuda/ldsm.h>
#include <tl_templates/cuda/threadblock_swizzle.h>
#include <tl_templates/cuda/debug.h>
#include <tl_templates/cuda/intrin.h>
#include <tl_templates/cuda/distributed.h>
#include <tl_templates/cuda/sync.h>
#include <tl_templates/cuda/ldst.h>
extern "C" __constant__ uint64_t meta_data[1024];
#ifdef ENABLE_BF16
#include <tl_templates/cuda/cuda_bf16_fallbacks.cuh>
#endif

extern "C" __global__ void combine_main_kernel(int* __restrict__ channel_head_idx, const int* __restrict__ channel_prefix_matrix, int* __restrict__ channel_src_idx_buffers, int* __restrict__ channel_tail_idx, float* __restrict__ channel_topk_weights_buffers, bfloat16_t* __restrict__ channel_x_buffers, const int* __restrict__ rank_prefix_matrix, float* __restrict__ recv_topk_weights, bfloat16_t* __restrict__ recv_x, int* __restrict__ send_head, int* __restrict__ src_idx, float* __restrict__ topk_weights, bfloat16_t* __restrict__ x, int num_recv_tokens, int num_tokens, int rank);
extern "C" __global__ void __launch_bounds__(768, 1) combine_main_kernel(int* __restrict__ channel_head_idx, const int* __restrict__ channel_prefix_matrix, int* __restrict__ channel_src_idx_buffers, int* __restrict__ channel_tail_idx, float* __restrict__ channel_topk_weights_buffers, bfloat16_t* __restrict__ channel_x_buffers, const int* __restrict__ rank_prefix_matrix, float* __restrict__ recv_topk_weights, bfloat16_t* __restrict__ recv_x, int* __restrict__ send_head, int* __restrict__ src_idx, float* __restrict__ topk_weights, bfloat16_t* __restrict__ x, int num_recv_tokens, int num_tokens, int rank) {
  int current_channel_tail_idx = 0;
  int token_idx = 0;
  int dst_slot_idx = 0;
  __shared__ int warp_retired[24];
  __shared__ int warp_channel_head_idx[48];
  __shared__ int shared_channel_tail_idx[32];
  int last_head = 0;
  signed char retired = (signed char)0;
  int new_tail = 0;
  int min_head = 0;
  int idx = 0;
  int head_i = 0;
  int slot_indices[2];
  int topk_ranks[2];
  float values[8];
  bfloat16_t recv_value[16];
  float weight_sum = 0x0p+0f/*0.000000e+00*/;
  float weight = 0x0p+0f/*0.000000e+00*/;
  if ((((int)blockIdx.x) % 2) == 0) {
    int condval;
    if ((((0 < (((((int)threadIdx.x) >> 5) + (((int)blockIdx.x) >> 1)) & 1)) && (0 <= rank)) && (rank < 2))) {
      condval = rank_prefix_matrix[((((((((int64_t)((int)threadIdx.x)) >> (int64_t)5) + (((int64_t)((int)blockIdx.x)) >> (int64_t)1)) & (int64_t)1) * (int64_t)2) + ((int64_t)rank)) - (int64_t)2)];
    } else {
      condval = 0;
    }
    int rank_offset = condval;
    int condval_1;
    if (((0 <= rank) && (rank < 2))) {
      condval_1 = rank_prefix_matrix[(((((((int64_t)((int)threadIdx.x)) >> (int64_t)5) + (((int64_t)((int)blockIdx.x)) >> (int64_t)1)) & (int64_t)1) * (int64_t)2) + ((int64_t)rank))];
    } else {
      condval_1 = 0;
    }
    int num_rank_tokens = (condval_1 - rank_offset);
    int channel_offset = channel_prefix_matrix[(((((((int)threadIdx.x) >> 5) + (((int)blockIdx.x) >> 1)) & 1) * 10) + (((int)blockIdx.x) >> 1))];
    int condval_2;
    if (((((int)blockIdx.x) >> 1) == 9)) {
      condval_2 = num_rank_tokens;
    } else {
      condval_2 = channel_prefix_matrix[((((((((int)threadIdx.x) >> 5) + (((int)blockIdx.x) >> 1)) & 1) * 10) + (((int)blockIdx.x) >> 1)) + 1)];
    }
    int num_channel_tokens = (condval_2 - channel_offset);
    current_channel_tail_idx = 0;
    token_idx = (rank_offset + channel_offset);
    while (1) {
      if (!((token_idx < ((rank_offset + channel_offset) + num_channel_tokens)))) { break; }
      int num_round_tokens = min(10, (((rank_offset + channel_offset) + num_channel_tokens) - token_idx));
      if (tl::tl_shuffle_elect<32>()) {
        if (0 <= rank) {
          if (rank < 2) {
            tl::wait_ge((tl::get_remote_base_ptr((((((int)threadIdx.x) >> 5) + (((int)blockIdx.x) >> 1)) & 1)) + (tl::get_uintptr_t((&(channel_head_idx[(((((int)blockIdx.x) >> 1) * 2) + rank)]))) - tl::get_remote_base_ptr(tl::get_rank()))), ((current_channel_tail_idx + num_round_tokens) - 256));
          }
        }
      }
      __syncwarp();
      for (int _tmp = 0; _tmp < ((((num_round_tokens + 11) - (((int)threadIdx.x) >> 6)) / 12) + ((((num_round_tokens + 11) - (((int)threadIdx.x) >> 6)) % 12) >> 31)); ++_tmp) {
        dst_slot_idx = ((((_tmp * 12) + (((int)threadIdx.x) >> 6)) + current_channel_tail_idx) & 255);
        if (0 <= (((_tmp * 12) + (((int)threadIdx.x) >> 6)) + token_idx)) {
          if ((((_tmp * 12) + (((int)threadIdx.x) >> 6)) + token_idx) < num_tokens) {
            if (0 <= dst_slot_idx) {
              if (dst_slot_idx < 256) {
                if (0 <= rank) {
                  if (rank < 2) {
                    tl::cp_warp<64, 4, true>((tl::get_remote_base_ptr((((((int)threadIdx.x) >> 5) + (((int)blockIdx.x) >> 1)) & 1)) + (tl::get_uintptr_t((&(channel_x_buffers[((((((int)blockIdx.x) >> 1) * 32768) + (rank * 16384)) + (dst_slot_idx * 64))]))) - tl::get_remote_base_ptr(tl::get_rank()))), (&(x[(((((int64_t)_tmp) * (int64_t)768) + ((((int64_t)((int)threadIdx.x)) >> (int64_t)6) * (int64_t)64)) + (((int64_t)token_idx) * (int64_t)64))])));
                  }
                }
              }
            }
          }
        }
        if (tl::tl_shuffle_elect<32>()) {
          if (0 <= (((_tmp * 12) + (((int)threadIdx.x) >> 6)) + token_idx)) {
            if ((((_tmp * 12) + (((int)threadIdx.x) >> 6)) + token_idx) < num_tokens) {
              tl::ld<Semantic::WEAK, Scope::GPU, true, false>((&(src_idx[(((((int64_t)_tmp) * (int64_t)12) + (((int64_t)((int)threadIdx.x)) >> (int64_t)6)) + ((int64_t)token_idx))])), idx);
            }
          }
          if (0 <= dst_slot_idx) {
            if (dst_slot_idx < 256) {
              if (0 <= rank) {
                if (rank < 2) {
                  tl::st<Semantic::WEAK, Scope::GPU, false>((tl::get_remote_base_ptr((((((int)threadIdx.x) >> 5) + (((int)blockIdx.x) >> 1)) & 1)) + (tl::get_uintptr_t((&(channel_src_idx_buffers[((((((int)blockIdx.x) >> 1) * 512) + (rank * 256)) + dst_slot_idx)]))) - tl::get_remote_base_ptr(tl::get_rank()))), idx);
                }
              }
            }
          }
        }
        if ((((int)threadIdx.x) & 31) < 2) {
          if (0 <= (((_tmp * 12) + (((int)threadIdx.x) >> 6)) + token_idx)) {
            if ((((_tmp * 12) + (((int)threadIdx.x) >> 6)) + token_idx) < num_tokens) {
              tl::ld<Semantic::WEAK, Scope::GPU, true, false>((&(topk_weights[((((((int64_t)_tmp) * (int64_t)24) + ((((int64_t)((int)threadIdx.x)) >> (int64_t)6) * (int64_t)2)) + (((int64_t)token_idx) * (int64_t)2)) + (((int64_t)((int)threadIdx.x)) & (int64_t)31))])), idx);
            }
          }
          if (0 <= dst_slot_idx) {
            if (dst_slot_idx < 256) {
              if (0 <= rank) {
                if (rank < 2) {
                  tl::st<Semantic::WEAK, Scope::GPU, false>((tl::get_remote_base_ptr((((((int)threadIdx.x) >> 5) + (((int)blockIdx.x) >> 1)) & 1)) + (tl::get_uintptr_t((&(channel_topk_weights_buffers[(((((((int)blockIdx.x) >> 1) * 1024) + (rank * 512)) + (dst_slot_idx * 2)) + (((int)threadIdx.x) & 31))]))) - tl::get_remote_base_ptr(tl::get_rank()))), idx);
                }
              }
            }
          }
        }
      }
      token_idx = (token_idx + num_round_tokens);
      current_channel_tail_idx = (current_channel_tail_idx + num_round_tokens);
      tl::__sync_thread_partial((((((int)threadIdx.x) >> 5) + (((int)blockIdx.x) >> 1)) & 1), 384);
      if (tl::tl_shuffle_elect<96>()) {
        if (0 <= rank) {
          if (rank < 2) {
            tl::st<Semantic::RELEASE, Scope::SYS, false>((tl::get_remote_base_ptr((((((int)threadIdx.x) >> 5) + (((int)blockIdx.x) >> 1)) & 1)) + (tl::get_uintptr_t((&(channel_tail_idx[(((((int)blockIdx.x) >> 1) * 2) + rank)]))) - tl::get_remote_base_ptr(tl::get_rank()))), current_channel_tail_idx);
          }
        }
      }
    }
  } else {
    if (((int)threadIdx.x) < 24) {
      warp_retired[((int)threadIdx.x)] = 0;
    }
    if ((((int)threadIdx.x) & 31) < 2) {
      warp_channel_head_idx[(((((int)threadIdx.x) >> 5) * 2) + (((int)threadIdx.x) & 31))] = 0;
    }
    if (((int)threadIdx.x) < 32) {
      shared_channel_tail_idx[((int)threadIdx.x)] = 0;
    }
    __syncthreads();
    if (((int)threadIdx.x) < 32) {
      last_head = 0;
      while (1) {
        if (!((((int)threadIdx.x) < 2))) { break; }
        retired = (signed char)1;
        for (int i = 1; i < 24; ++i) {
          tl::ld<Semantic::ACQUIRE, Scope::CTA, false, false>((&(warp_retired[i])), idx);
          retired = ((signed char)(((bool)retired) && (idx != 0)));
        }
        if ((bool)retired) {
          break;;
        }
        if (((int)threadIdx.x) < 2) {
          tl::ld<Semantic::ACQUIRE, Scope::SYS, false, false>((&(channel_tail_idx[(((((int)blockIdx.x) >> 1) * 2) + ((int)threadIdx.x))])), new_tail);
        }
        tl::st<Semantic::RELEASE, Scope::CTA, false>((&(shared_channel_tail_idx[((int)threadIdx.x)])), new_tail);
        min_head = 2147483647;
        for (int i_1 = 1; i_1 < 24; ++i_1) {
          tl::ld<Semantic::ACQUIRE, Scope::CTA, false, false>((&(warp_retired[i_1])), idx);
          if (idx == 0) {
            tl::ld<Semantic::ACQUIRE, Scope::CTA, false, false>((&(warp_channel_head_idx[((i_1 * 2) + ((int)threadIdx.x))])), head_i);
            min_head = min(min_head, head_i);
          }
        }
        if ((min_head < 2147483647) && (last_head < min_head)) {
          last_head = min_head;
          if (((int)threadIdx.x) < 2) {
            tl::st<Semantic::RELEASE, Scope::SYS, false>((&(channel_head_idx[(((((int)blockIdx.x) >> 1) * 2) + ((int)threadIdx.x))])), min_head);
          }
        }
      }
    } else {
      for (int _tmp_1 = 0; _tmp_1 < ((((min(((num_recv_tokens + 9) / 10), max((num_recv_tokens - (((num_recv_tokens + 9) / 10) * (((int)blockIdx.x) >> 1))), 0)) - (((int)threadIdx.x) >> 5)) / 23) + (((min(((num_recv_tokens + 9) / 10), max((num_recv_tokens - (((num_recv_tokens + 9) / 10) * (((int)blockIdx.x) >> 1))), 0)) - (((int)threadIdx.x) >> 5)) % 23) >> 31)) + 1); ++_tmp_1) {
        token_idx = ((((_tmp_1 * 23) + min((((num_recv_tokens + 9) / 10) * (((int)blockIdx.x) >> 1)), num_recv_tokens)) + (((int)threadIdx.x) >> 5)) - 1);
        idx = -1;
        if ((((int)threadIdx.x) & 31) < 2) {
          if (0 <= token_idx) {
            if (token_idx < num_recv_tokens) {
              tl::ld<Semantic::WEAK, Scope::GPU, true, false>((&(send_head[((((int64_t)token_idx) * (int64_t)2) + (((int64_t)((int)threadIdx.x)) & (int64_t)31))])), idx);
            }
          }
        }
        tl::ld<Semantic::ACQUIRE, Scope::CTA, false, false>((&(shared_channel_tail_idx[(((int)threadIdx.x) & 31)])), head_i);
        while (1) {
          if (!(__any_sync(-1, ((head_i <= idx) && (0 <= idx))))) { break; }
          tl::ld<Semantic::ACQUIRE, Scope::CTA, false, false>((&(shared_channel_tail_idx[(((int)threadIdx.x) & 31)])), head_i);
          continue;;
        }
        __syncwarp();
        head_i = 0;
        for (int i_2 = 0; i_2 < 2; ++i_2) {
          int expected_head_i = __shfl_sync(-1, idx, i_2, 32);
          if (0 <= expected_head_i) {
            slot_indices[head_i] = (expected_head_i & 255);
            topk_ranks[head_i] = i_2;
            head_i = (head_i + 1);
          }
        }
        for (int _tmp_2 = 0; _tmp_2 < ((39 - (((int)threadIdx.x) & 31)) >> 5); ++_tmp_2) {
          for (int i_3 = 0; i_3 < 2; ++i_3) {
            *(float4*)(values + (i_3 * 4)) = make_float4(0x0p+0f/*0.000000e+00*/, 0x0p+0f/*0.000000e+00*/, 0x0p+0f/*0.000000e+00*/, 0x0p+0f/*0.000000e+00*/);
          }
          for (int j = 0; j < head_i; ++j) {
            if (0 <= slot_indices[j]) {
              if (slot_indices[j] < 256) {
                if (0 <= topk_ranks[j]) {
                  if (topk_ranks[j] < 2) {
                    tl::ld<Semantic::WEAK, Scope::GPU, true, false>((&(channel_x_buffers[((((((((int)blockIdx.x) >> 1) * 32768) + (topk_ranks[j] * 16384)) + (_tmp_2 * 256)) + (slot_indices[j] * 64)) + ((((int)threadIdx.x) & 31) * 8))])), *(uint4*)(recv_value + (((int64_t)j) * (int64_t)8)));
                  }
                }
              }
            }
          }
          for (int j_1 = 0; j_1 < head_i; ++j_1) {
            for (int k = 0; k < 2; ++k) {
              float4 __1;
                float4 v_ = *(float4*)(values + (k * 4));
                float4 __2;
                uint2 v__1 = *(uint2*)(recv_value + ((((int64_t)j_1) * (int64_t)8) + (((int64_t)k) * (int64_t)4)));
                ((float2*)(&__2))[0] = __bfloat1622float2((reinterpret_cast<__nv_bfloat162*>(&v__1))[0]);
                ((float2*)(&__2))[1] = __bfloat1622float2((reinterpret_cast<__nv_bfloat162*>(&v__1))[1]);
                __1.x = (v_.x+__2.x);
                __1.y = (v_.y+__2.y);
                __1.z = (v_.z+__2.z);
                __1.w = (v_.w+__2.w);
              *(float4*)(values + (k * 4)) = __1;
            }
          }
          for (int j_2 = 0; j_2 < 2; ++j_2) {
            if (0 <= token_idx) {
              if (token_idx < num_recv_tokens) {
                uint2 __3;
                float4 v__2 = *(float4*)(values + (j_2 * 4));
                (reinterpret_cast<__nv_bfloat162*>(&__3))[0] = __float22bfloat162_rn(((float2*)(&v__2))[0]);
                (reinterpret_cast<__nv_bfloat162*>(&__3))[1] = __float22bfloat162_rn(((float2*)(&v__2))[1]);
                *(uint2*)(recv_x + ((((((int64_t)_tmp_2) * (int64_t)256) + (((int64_t)token_idx) * (int64_t)64)) + ((((int64_t)((int)threadIdx.x)) & (int64_t)31) * (int64_t)8)) + (((int64_t)j_2) * (int64_t)4))) = __3;
              }
            }
          }
        }
        if ((((int)threadIdx.x) & 31) < 2) {
          weight_sum = 0x0p+0f/*0.000000e+00*/;
          for (int i_4 = 0; i_4 < head_i; ++i_4) {
            if (0 <= slot_indices[i_4]) {
              if (slot_indices[i_4] < 256) {
                if (0 <= topk_ranks[i_4]) {
                  if (topk_ranks[i_4] < 2) {
                    tl::ld<Semantic::WEAK, Scope::GPU, true, false>((&(channel_topk_weights_buffers[(((((((int)blockIdx.x) >> 1) * 1024) + (topk_ranks[i_4] * 512)) + (slot_indices[i_4] * 2)) + (((int)threadIdx.x) & 31))])), weight);
                  }
                }
              }
            }
            weight_sum = (weight_sum + weight);
          }
          if (0 <= token_idx) {
            if (token_idx < num_recv_tokens) {
              recv_topk_weights[((((int64_t)token_idx) * (int64_t)2) + (((int64_t)((int)threadIdx.x)) & (int64_t)31))] = weight_sum;
            }
          }
          int condval_3;
          if ((idx < 0)) {
            condval_3 = ((0 - idx) - 1);
          } else {
            condval_3 = (idx + 1);
          }
          tl::st<Semantic::RELEASE, Scope::CTA, false>((&(warp_channel_head_idx[(((((int)threadIdx.x) >> 5) * 2) + (((int)threadIdx.x) & 31))])), condval_3);
        }
      }
      __syncwarp();
      if (tl::tl_shuffle_elect<32>()) {
        tl::st<Semantic::RELEASE, Scope::CTA, false>((&(warp_retired[(((int)threadIdx.x) >> 5)])), 1);
      }
    }
  }
}

