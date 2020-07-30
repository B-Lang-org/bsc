// The MIT License

// Copyright (c) 2006-2007 Massachusetts Institute of Technology

// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:

// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.
import GetPut::*;
import H264Types::*;



module mkEntropyTee#(Get#(EntropyDecOT) inputData, Put#(EntropyDecOT) outputData, String prefix) ();

 rule processDisplay;
   let dataIn <- inputData.get(); 
   outputData.put(dataIn);
   $write(prefix);
   $write("BIN ");
   $display("%h", pack(dataIn));

   $write(prefix);
   case (dataIn) matches
     tagged  NewUnit .nu: $display("NewUnit: %d", nu);
     tagged  SPSseq_parameter_set_id .data: $display("SPSseq_parameter_set_id: %d",data);
     tagged  SPSlog2_max_frame_num .data: $display("SPSlog2_max_frame_num: %d",data);
     tagged  SPSpic_order_cnt_type .data: $display("SPSpic_order_cnt_type: %d",data);
     tagged  SPSlog2_max_pic_order_cnt_lsb .data: $display("SPSlog2_max_pic_order_cnt_lsb: %d",data);
     tagged  SPSdelta_pic_order_always_zero_flag .data: $display("SPSdelta_pic_order_always_zero_flag: %d",data);
     tagged  SPSoffset_for_non_ref_pic .data: $display("SPSoffset_for_non_ref_pic: %d",data);
     tagged  SPSoffset_for_top_to_bottom_field .data: $display("SPSoffset_for_top_to_bottom_field: %d",data);
     tagged  SPSnum_ref_frames_in_pic_order_cnt_cycle .data: $display("SPSnum_ref_frames_in_pic_order_cnt_cycle: %d",data);
     tagged  SPSoffset_for_ref_frame .data: $display("SPSoffset_for_ref_frame: %d",data);
     tagged  SPSnum_ref_frames .data: $display("SPSnum_ref_frames: %d",data);
     tagged  SPSgaps_in_frame_num_allowed_flag .data: $display("SPSgaps_in_frame_num_allowed_flag: %d",data);
     tagged  SPSpic_width_in_mbs .data: $display("SPSpic_width_in_mbs: %d",data);
     tagged  SPSpic_height_in_map_units .data: $display("SPSpic_height_in_map_units: %d",data);
     tagged  SPSdirect_8x8_inference_flag .data: $display("SPSdirect_8x8_inference_flag: %d",data);
     tagged  SPSframe_cropping_flag .data: $display("SPSframe_cropping_flag: %d",data);
     tagged  SPSframe_crop_left_offset .data: $display("SPSframe_crop_left_offset: %d",data);
     tagged  SPSframe_crop_right_offset .data: $display("SPSframe_crop_right_offset: %d",data);
     tagged  SPSframe_crop_top_offset .data: $display("SPSframe_crop_top_offset: %d",data);
     tagged  SPSframe_crop_bottom_offset .data: $display("SPSframe_crop_bottom_offset: %d",data);
     tagged  PPSpic_parameter_set_id .data: $display("PPSpic_parameter_set_id: %d",data);
     tagged  PPSseq_parameter_set_id .data: $display("PPSseq_parameter_set_id: %d",data);
     tagged  PPSpic_order_present_flag .data: $display("PPSpic_order_present_flag: %d",data);
     tagged  PPSnum_ref_idx_l0_active .data: $display("PPSnum_ref_idx_l0_active: %d",data);
     tagged  PPSnum_ref_idx_l1_active .data: $display("PPSnum_ref_idx_l1_active: %d",data);
     tagged  PPSdeblocking_filter_control_present_flag .data: $display("PPSdeblocking_filter_control_present_flag: %d",data);
     tagged  PPSconstrained_intra_pred_flag .data: $display("PPSconstrained_intra_pred_flag: %d",data);
     tagged  SHfirst_mb_in_slice .data: $display("SHfirst_mb_in_slice: %d",data);
     tagged  SHslice_type .data: $display("SHslice_type: %d",data);
     tagged  SHpic_parameter_set_id .data: $display("SHpic_parameter_set_id: %d",data);
     tagged  SHframe_num .data: $display("SHframe_num: %d",data);
     tagged  SHidr_pic_id .data: $display("SHidr_pic_id: %d",data);
     tagged  SHpic_order_cnt_lsb .data: $display("SHpic_order_cnt_lsb: %d",data);
     tagged  SHdelta_pic_order_cnt_bottom .data: $display("SHdelta_pic_order_cnt_bottom: %d",data);
     tagged  SHdelta_pic_order_cnt0 .data: $display("SHdelta_pic_order_cnt0: %d",data);
     tagged  SHdelta_pic_order_cnt1 .data: $display("SHdelta_pic_order_cnt1: %d",data);
     tagged  SHnum_ref_idx_active_override_flag .data: $display("SHnum_ref_idx_active_override_flag: %d",data);
     tagged  SHnum_ref_idx_l0_active .data: $display("SHnum_ref_idx_l0_active: %d",data);
     tagged  SHRref_pic_list_reordering_flag_l0 .data: $display("HRref_pic_list_reordering_flag_l0: %d",data);
     tagged  SHRreordering_of_pic_nums_idc .data: $display("SHRreordering_of_pic_nums_idc: %d",data);
     tagged  SHRabs_diff_pic_num .data: $display("SHRabs_diff_pic_num: %d",data);
     tagged  SHRlong_term_pic_num .data: $display("SHRlong_term_pic_num: %d",data);
     tagged  SHDno_output_of_prior_pics_flag .data: $display("SHDno_output_of_prior_pics_flag: %d",data);
     tagged  SHDlong_term_reference_flag .data: $display("SHDlong_term_reference_flag: %d",data);
     tagged  SHDadaptive_ref_pic_marking_mode_flag .data: $display("SHDadaptive_ref_pic_marking_mode_flag: %d",data);
     tagged  SHDmemory_management_control_operation .data: $display("SHDmemory_management_control_operation: %d",data);
     tagged  SHDdifference_of_pic_nums .data: $display("SHDdifference_of_pic_nums: %d",data);
     tagged  SHDlong_term_pic_num .data: $display("SHDlong_term_pic_num: %d",data);
     tagged  SHDlong_term_frame_idx .data: $display("SHDlong_term_frame_idx: %d",data);
     tagged  SHDmax_long_term_frame_idx_plus1 .data: $display("SHDmax_long_term_frame_idx_plus1: %d",data);
     tagged  SHdisable_deblocking_filter_idc .data: $display("SHdisable_deblocking_filter_idc: %d",data);
     tagged  SHslice_alpha_c0_offset .data: $display("SHslice_alpha_c0_offset: %d",data);
     tagged  SHslice_beta_offset .data: $display("SHslice_beta_offset: %d",data);
     tagged  SDmb_skip_run .data: $display("SDmb_skip_run: %d",data);
     tagged  SDMmbtype .data: $display("SDMmbtype: %d",data);
     tagged  SDMpcm_sample_luma .data: $display("SDMpcm_sample_luma: %d",data);
     tagged  SDMpcm_sample_chroma .data: $display("SDMpcm_sample_chroma: %d",data);
     tagged  SDMMrem_intra4x4_pred_mode .data: $display("SDMMrem_intra4x4_pred_mode: %d",data);
     tagged  SDMMintra_chroma_pred_mode .data: $display("SDMMintra_chroma_pred_mode: %d",data);
     tagged  SDMMref_idx_l0 .data: $display("SDMMref_idx_l0: %d",data);
     tagged  SDMMmvd_l0 .data: $display("SDMMmvd_l0: %d",data);
     tagged  SDMSsub_mb_type .data: $display("SDMSsub_mb_type: %d",data);
     tagged  SDMSref_idx_l0 .data: $display("SDMSref_idx_l0: %d",data);
     tagged  SDMSmvd_l0 .data: $display("SDMSmvd_l0: %d",data);
     tagged  IBTmb_qp .qps: $display("IBTmb_qp: qpy: %d qpc: %d", qps.qpy, qps.qpc);
     tagged  PBbS .pbs: $display("PBbS: bSHor: %d bSVer: %d", pbs.bShor, pbs.bSver);
     tagged  PBoutput .vec: $display("PBoutput: %h %h %h %h", vec[0],vec[1],vec[2],vec[3]); 
     tagged  AUDPrimaryPicType .data: $display("AUDPrimaryPicType: %d",data);
     tagged  EndOfSequence: $display("EndOfSequence");
     tagged  EndOfStream: $display("EndOfStream");
     tagged  EndOfFile: $display("EndOfFile");
   endcase  
 endrule   
endmodule