/* Bit Stream Parser parses the MPEG4 stream and performs VLD,
   inverse scan,inverse quantisation , AC/DC prediction , 
   MV  prediction in the MPEG-4 decoder.
*/

package BtStrmPrsr;
import FIFOF::* ;
import ConfigReg :: *;
import RegFile :: *;
import List :: *;
import Defines :: *;
import ByteAlign :: *;
import CBuffer :: *;
import DetstartCode :: *;
import Inverse_Quantization :: *;
import FLCDecode :: *;
import Division :: *;
import MVarith :: *;

interface BtStrmPrsr_IFC;
  method Action get_host_strobe (Bit#(1) host_strobe) ;
  method Action get_host_select (Bit#(2) host_select) ;
  method Action get_host_address (Bit#(8) host_address) ;
  method Action get_host_datain (Bit#(8) host_datain) ;
  method Action get_vd_valid (Bit#(1) vd_valid) ;
  method Action get_vd_data  (Bit#(8) vd_data) ;
  method Action get_rdmv  (Bit#(1) rd_mv) ;
  method Action get_mb_done (Bit#(1) mb_done) ;
  method Bit#(1) vd_rd () ;
  method Bit#(12) dct_data_out () ;
  method Bit#(1)  dct_data_valid () ;
  method Bit#(1)  hdr_rdy () ;
  method Bool     busy () ;
  method Bool     vop_done () ;
  method Bit#(1)  disable_mb_done () ;
  method Mbheadertype  header_data () ;
  //method Bit#(1)  mb_coded () ;

endinterface : BtStrmPrsr_IFC

(* synthesize ,
   CLK = "clk",
   RST_N = "reset"
*)

module mkBtStrmPrsr (BtStrmPrsr_IFC);

  RWire#(Bit#(1))   host_strobe();
  mkRWire           t_host_strobe(host_strobe);

  RWire#(Bit#(2))   host_select();
  mkRWire           t_host_select(host_select);

  RWire#(Bit#(8))   host_address();
  mkRWire           t_host_address(host_address);

  RWire#(Bit#(8))   host_datain();
  mkRWire           t_host_datain(host_datain);

  RWire#(Bit#(1))   vd_valid();
  mkRWire           t_vd_valid(vd_valid);

  RWire#(Bit#(8))   vd_data();
  mkRWire           t_vd_data(vd_data);

  RWire#(Bit#(1))   rdmv();
  mkRWire           t_rdmv(rdmv);

  RWire#(Bit#(1))   mb_done();
  mkRWire           t_mb_done(mb_done);

  Reg#(PSstates)     sysState();
  mkConfigReg#(IDLE) the_sysState(sysState);

  Reg#(VideoSt)  videoSt();
  mkReg#(IDLE)   the_videoSt(videoSt);

  Reg#(FLC_type)  flc_type();
  mkReg#(NOTUSED)   the_flc_type(flc_type);

//  Reg#(StartCodeSt)  strtcodeSt();
//  mkReg#(IDLE)   the_strtcodeSt(strtcodeSt);

  Reg#(Bit#(1))  vd_rd_reg();
  mkReg#(0)      the_vd_rd_reg(vd_rd_reg);

  Reg#(Bit#(4))  byte_align_pos();
  mkReg#(0)      the_byte_align_pos(byte_align_pos);

  Reg#(Bit#(5))  byte_offset();
  mkReg#(0)      the_byte_offset(byte_offset);

  Reg#(Bit#(5))  byte_offset_check();
  mkReg#(0)      the_byte_offset_check(byte_offset_check);

  ConfigReg#(Bit#(40))  start_code_reg();
  mkConfigReg#(0)      the_start_code_reg(start_code_reg);

  Reg#(Bit#(8))  tmp_in_data();
  mkReg#(0)      the_tmp_in_data(tmp_in_data);

  Reg#(Bit#(3))  cnt();
  mkReg#(0)      the_cnt(cnt);

  Reg#(Bit#(10)) wait_cnt();
  mkReg#(0)      the_wait_cnt(wait_cnt);

//  Reg#(Bool)     isVideoObjectLayer();
//  mkReg#(False)  the_isVideoObjectLayer(isVideoObjectLayer);

  Reg#(Bit#(8))  diff_buffer();
  mkReg#(0)      the_diff_buffer(diff_buffer);

  Reg#(Bool)     short_video_header();
  mkReg#(False)  the_short_video_header(short_video_header);

  Reg#(Bit#(5))  video_object_number();
  mkReg#(0)      the_video_object_number(video_object_number);

  Reg#(Bit#(4))  vol_number();
  mkReg#(0)      the_vol_number(vol_number);

  Reg#(Bit#(1))  random_accessible_vol();
  mkReg#(0)      the_random_accessible_vol(random_accessible_vol);

  Reg#(Bit#(8))  video_object_type_indication();
  mkReg#(0)      the_video_object_type_indication(video_object_type_indication);

  Reg#(Bit#(1))  is_object_layer_identifier();
  mkReg#(0)      the_is_object_layer_identifier(is_object_layer_identifier);

// when this field is non-existing its default value is 1
  Reg#(Bit#(4))  video_object_layer_verid();
  mkReg#(1)      the_video_object_layer_verid(video_object_layer_verid);

  Reg#(Bit#(3))  video_object_layer_priority();
  mkReg#(0)      the_video_object_layer_priority(video_object_layer_priority);

  Reg#(Bit#(4))  aspect_ratio_info();
  mkReg#(0)      the_aspect_ratio_info(aspect_ratio_info);

  Reg#(Bit#(8))  par_width();
  mkReg#(0)      the_par_width(par_width);

  Reg#(Bit#(8))  par_heigth();
  mkReg#(0)      the_par_heigth(par_heigth);

  Reg#(Bit#(1))  vol_control_parameters();
  mkReg#(0)      the_vol_control_parameters(vol_control_parameters);

  Reg#(Bit#(2))  chroma_format();
  mkReg#(0)      the_chroma_format(chroma_format);

  Reg#(Bit#(1))  low_delay();
  mkReg#(0)      the_low_delay(low_delay);

  Reg#(Bit#(1))  vbv_parameters();
  mkReg#(0)      the_vbv_parameters(vbv_parameters);

  Reg#(Bit#(15)) first_half_bit_rate();
  mkReg#(0)      the_first_half_bit_rate(first_half_bit_rate);

  Reg#(Bit#(15)) latter_half_bit_rate();
  mkReg#(0)      the_latter_half_bit_rate(latter_half_bit_rate);

  Reg#(Bit#(15)) first_half_vbv_buffer_size();
  mkReg#(0)      the_first_half_vbv_buffer_size(first_half_vbv_buffer_size);

  Reg#(Bit#(3))  latter_half_vbv_buffer_size();
  mkReg#(0)      the_latter_half_vbv_buffer_size(latter_half_vbv_buffer_size);

  Reg#(Bit#(11)) first_half_vbv_occupancy();
  mkReg#(0)      the_first_half_vbv_occupancy(first_half_vbv_occupancy);

  Reg#(Bit#(15))  latter_half_vbv_occupancy();
  mkReg#(0)      the_latter_half_vbv_occupancy(latter_half_vbv_occupancy);

  Reg#(Bit#(1))  marker_bit();
  mkReg#(0)      the_marker_bit(marker_bit);

  Reg#(Bit#(2))  video_object_layer_shape();
  mkReg#(0)      the_video_object_layer_shape(video_object_layer_shape);

  Reg#(Bit#(4))  video_object_layer_shape_extension();
  mkReg#(0)      the_video_object_layer_shape_extension(video_object_layer_shape_extension);

  Reg#(Bit#(16)) vop_time_increment_resolution();
  mkReg#(0)      the_vop_time_increment_resolution(vop_time_increment_resolution);

  Reg#(Bit#(16)) tmp_vop_time_increment_resolution();
  mkReg#(0)      the_tmp_vop_time_increment_resolution(tmp_vop_time_increment_resolution);

  Reg#(Bit#(1))  fixed_vop_rate();
  mkReg#(0)      the_fixed_vop_rate(fixed_vop_rate);

  Reg#(Bit#(16)) fixed_vop_time_increment();
  mkReg#(0)      the_fixed_vop_time_increment(fixed_vop_time_increment);

  Reg#(Bit#(13)) video_object_layer_width();
  mkReg#(0)      the_video_object_layer_width(video_object_layer_width);

  Reg#(Bit#(13)) video_object_layer_height();
  mkReg#(0)      the_video_object_layer_height(video_object_layer_height);

  Reg#(Bit#(9))  mb_width();
  mkReg#(0)      the_mb_width(mb_width);

  Reg#(Bit#(9))  mb_height();
  mkReg#(0)      the_mb_height(mb_height);

  Reg#(Bit#(1))  interlaced();
  mkReg#(0)      the_interlaced(interlaced);

  Reg#(Bit#(1))  obmc_disable();
  mkReg#(0)      the_obmc_disable(obmc_disable);

  Reg#(Bit#(2))  sprite_enable();
  mkReg#(0)      the_sprite_enable(sprite_enable);

  Reg#(Bit#(13)) sprite_width();
  mkReg#(0)      the_sprite_width(sprite_width);

  Reg#(Bit#(13)) sprite_height();
  mkReg#(0)      the_sprite_height(sprite_height);

  Reg#(Bit#(13)) sprite_left_coordinate();
  mkReg#(0)      the_sprite_left_coordinate(sprite_left_coordinate);

  Reg#(Bit#(13)) sprite_top_coordinate();
  mkReg#(0)      the_sprite_top_coordinate(sprite_top_coordinate);

  Reg#(Bit#(6))  no_of_sprite_warping_points();
  mkReg#(0)      the_no_of_sprite_warping_points(no_of_sprite_warping_points);

  Reg#(Bit#(2))  sprite_warping_accuracy();
  mkReg#(0)      the_sprite_warping_accuracy(sprite_warping_accuracy);

  Reg#(Bit#(1))  sprite_brightness_change();
  mkReg#(0)      the_sprite_brightness_change(sprite_brightness_change);

  Reg#(Bit#(1))  low_latency_sprite_enable();
  mkReg#(0)      the_low_latency_sprite_enable(low_latency_sprite_enable);

  Reg#(Bit#(1))  sadct_disable();
  mkReg#(0)      the_sadct_disable(sadct_disable);

  Reg#(Bit#(1))  not_8_bit();
  mkReg#(0)      the_not_8_bit(not_8_bit);

  Reg#(Bit#(4))  quant_precision();
  mkReg#(5)      the_quant_precision(quant_precision);

  Reg#(Bit#(4))  bits_per_pixel();
  mkReg#(0)      the_bits_per_pixel(bits_per_pixel);

  Reg#(Bit#(1))  no_gray_quant_update();
  mkReg#(0)      the_no_gray_quant_update(no_gray_quant_update);

  Reg#(Bit#(1))  composition_method();
  mkReg#(0)      the_composition_method(composition_method);

  Reg#(Bit#(1))  linear_composition();
  mkReg#(0)      the_linear_composition(linear_composition);

  Reg#(Bit#(1))  quant_type();
  mkReg#(0)      the_quant_type(quant_type);

  Reg#(Bit#(1))  load_intra_quant_mat();
  mkReg#(0)      the_load_intra_quant_mat(load_intra_quant_mat);

  Reg#(Bit#(1))  load_nonintra_quant_mat();
  mkReg#(0)      the_load_nonintra_quant_mat(load_nonintra_quant_mat);

  RegFile#(Bit#(6),Bit#(8)) intra_quant_mat();
  mkRegFileLoad#("QUANT_TABLES/intra_quant_matrix.txt",0,63)  the_intra_quant_mat(intra_quant_mat);

  RegFile#(Bit#(6),Bit#(8)) non_intra_quant_mat();
  mkRegFileLoad#("QUANT_TABLES/non_intra_quant_matrix.txt",0,63)  the_non_intra_quant_mat(non_intra_quant_mat);

  Reg#(Bit#(1))  load_intra_quant_mat_grayscale();
  mkReg#(0)      the_load_intra_quant_mat_grayscale(load_intra_quant_mat_grayscale);

  Reg#(Bit#(1))  load_nonintra_quant_mat_grayscale();
  mkReg#(0)      the_load_nonintra_quant_mat_grayscale(load_nonintra_quant_mat_grayscale);

  RegFile#(Bit#(6),Bit#(8)) intra_quant_mat_grayscale0();
  mkRegFileLoad#("QUANT_TABLES/intra_quant_matrix.txt",0,63)  the_intra_quant_mat_grayscale0(intra_quant_mat_grayscale0);

  RegFile#(Bit#(6),Bit#(8)) intra_quant_mat_grayscale1();
  mkRegFileLoad#("QUANT_TABLES/intra_quant_matrix.txt",0,63)  the_intra_quant_mat_grayscale1(intra_quant_mat_grayscale1);

  RegFile#(Bit#(6),Bit#(8)) intra_quant_mat_grayscale2();
  mkRegFileLoad#("QUANT_TABLES/intra_quant_matrix.txt",0,63)  the_intra_quant_mat_grayscale2(intra_quant_mat_grayscale2);

  RegFile#(Bit#(6),Bit#(8)) nonintra_quant_mat_grayscale0();
  mkRegFileLoad#("QUANT_TABLES/non_intra_quant_matrix.txt",0,63)  the_nonintra_quant_mat_grayscale0(nonintra_quant_mat_grayscale0);

  RegFile#(Bit#(6),Bit#(8)) nonintra_quant_mat_grayscale1();
  mkRegFileLoad#("QUANT_TABLES/non_intra_quant_matrix.txt",0,63)  the_nonintra_quant_mat_grayscale1(nonintra_quant_mat_grayscale1);

  RegFile#(Bit#(6),Bit#(8)) nonintra_quant_mat_grayscale2();
  mkRegFileLoad#("QUANT_TABLES/non_intra_quant_matrix.txt",0,63)  the_nonintra_quant_mat_grayscale2(nonintra_quant_mat_grayscale2);

  RegFile#(Bit#(32),Bit#(8)) user_data_buf();
  mkRegFile#(0,63)  the_user_data_buf(user_data_buf);

  Reg#(Bit#(1))  quarter_sample();
  mkReg#(0)      the_quarter_sample(quarter_sample);

  Reg#(Bit#(32))  user_data_counter();
  mkReg#(0)      the_user_data_counter(user_data_counter);

  Reg#(Bit#(2))  tmp_aux_cnt();
  mkReg#(0)      the_tmp_aux_cnt(tmp_aux_cnt);

  Reg#(Bit#(7))  counter();
  mkReg#(0)      the_counter(counter);

  Reg#(Bit#(5))  fvti_num();
  mkReg#(0)      the_fvti_num(fvti_num);

  Reg#(Bit#(3))  byte_boundary();
  mkReg#(0)      the_byte_boundary(byte_boundary);

  Reg#(Bool)     is_extended_par();
  mkReg#(False)  the_is_extended_par(is_extended_par);

  Reg#(Bit#(18)) time_code();
  mkReg#(0)      the_time_code(time_code);

  Reg#(Bit#(1))  closed_gov();
  mkReg#(0)      the_closed_gov(closed_gov);

  Reg#(Bit#(1))  broken_link();
  mkReg#(0)      the_broken_link(broken_link);

  Reg#(Bit#(2))  vop_coding_type();
  mkReg#(0)      the_vop_coding_type(vop_coding_type);

  Reg#(Bit#(1))  modulo_time_base();
  mkReg#(0)      the_modulo_time_base(modulo_time_base);

  Reg#(Bit#(3))  code_cnt();
  mkReg#(0)      the_code_cnt(code_cnt);

  Reg#(Bit#(1))  vop_reduced_resolution();
  mkReg#(0)      the_vop_reduced_resolution(vop_reduced_resolution);

  Reg#(Bit#(3))  intra_dc_vlc_thr();
  mkReg#(0)      the_intra_dc_vlc_thr(intra_dc_vlc_thr);

  Reg#(Bool)     use_intra_dc_vlc();
  mkReg#(False)  the_use_intra_dc_vlc(use_intra_dc_vlc);

  Reg#(Bit#(16)) vop_quant();
  mkReg#(0)      the_vop_quant(vop_quant);

  Reg#(Bit#(5))  quant_scale();
  mkReg#(0)      the_quant_scale(quant_scale);

  Reg#(Bit#(16)) running_QP();
  mkReg#(0)      the_running_QP(running_QP);

  Reg#(Bit#(16)) vop_shape_coding_type();
  mkReg#(0)      the_vop_shape_coding_type(vop_shape_coding_type);

  Reg#(Bit#(1))  complexity_estimation_disable();
  mkReg#(0)      the_complexity_estimation_disable(complexity_estimation_disable);

  Reg#(Bit#(1))  resync_marker_disable();
  mkReg#(0)      the_resync_marker_disable(resync_marker_disable);

  Reg#(Bit#(1))  data_partitioned();
  mkReg#(0)      the_data_partitioned(data_partitioned);

  Reg#(Bit#(1))  reversible_vlc();
  mkReg#(0)      the_reversible_vlc(reversible_vlc);

  Reg#(Bit#(1))  newpred_enable();
  mkReg#(0)      the_newpred_enable(newpred_enable);

  Reg#(Bit#(2))  requested_upstream_message_type();
  mkReg#(0)      the_requested_upstream_message_type(requested_upstream_message_type);

  Reg#(Bit#(1))  newpred_segment_type();
  mkReg#(0)      the_newpred_segment_type(newpred_segment_type);

  Reg#(Bit#(1))  reduced_resolution_vop_enable();
  mkReg#(0)      the_reduced_resolution_vop_enable(reduced_resolution_vop_enable);

  Reg#(Bit#(1))  scalability();
  mkReg#(0)      the_scalability(scalability);

  Reg#(Bit#(1))  hierarchy_type();
  mkReg#(0)      the_hierarchy_type(hierarchy_type);

  Reg#(Bit#(4))  ref_layer_id();
  mkReg#(0)      the_ref_layer_id(ref_layer_id);

  Reg#(Bit#(1))  ref_layer_sampling_direc();
  mkReg#(0)      the_ref_layer_sampling_direc(ref_layer_sampling_direc);

  Reg#(Bit#(5))  hor_sampling_factor_n();
  mkReg#(0)      the_hor_sampling_factor_n(hor_sampling_factor_n);

  Reg#(Bit#(5))  hor_sampling_factor_m();
  mkReg#(0)      the_hor_sampling_factor_m(hor_sampling_factor_m);

  Reg#(Bit#(5))  vert_sampling_factor_n();
  mkReg#(0)      the_vert_sampling_factor_n(vert_sampling_factor_n);

  Reg#(Bit#(5))  vert_sampling_factor_m();
  mkReg#(0)      the_vert_sampling_factor_m(vert_sampling_factor_m);

  Reg#(Bit#(1))  enhancement_type();
  mkReg#(0)      the_enhancement_type(enhancement_type);

  Reg#(Bit#(1))  use_ref_shape();
  mkReg#(0)      the_use_ref_shape(use_ref_shape);

  Reg#(Bit#(1))  use_ref_texture();
  mkReg#(0)      the_use_ref_texture(use_ref_texture);

  Reg#(Bit#(5))  shape_hor_sampling_factor_n();
  mkReg#(0)      the_shape_hor_sampling_factor_n(shape_hor_sampling_factor_n);

  Reg#(Bit#(5))  shape_hor_sampling_factor_m();
  mkReg#(0)      the_shape_hor_sampling_factor_m(shape_hor_sampling_factor_m);

  Reg#(Bit#(5))  shape_vert_sampling_factor_n();
  mkReg#(0)      the_shape_vert_sampling_factor_n(shape_vert_sampling_factor_n);

  Reg#(Bit#(5))  shape_vert_sampling_factor_m();
  mkReg#(0)      the_shape_vert_sampling_factor_m(shape_vert_sampling_factor_m);

  Reg#(Bit#(16)) vop_time_increment();
  mkReg#(0)      the_vop_time_increment(vop_time_increment);

  Reg#(Bit#(1))  vop_coded();
  mkReg#(0)      the_vop_coded(vop_coded);

  Reg#(Bit#(1))  vop_rounding_type();
  mkReg#(0)      the_vop_rounding_type(vop_rounding_type);

  Reg#(Bit#(3))  vop_fcode_forward();
  mkReg#(0)      the_vop_fcode_forward(vop_fcode_forward);

  Reg#(Bool)    first_MB();
  mkReg#(False) the_first_MB(first_MB);

  Reg#(Bit#(1))  not_coded();
  mkReg#(0)      the_not_coded(not_coded);

  Reg#(Bit#(3))  mbtype();
  mkReg#(0)      the_mbtype(mbtype);

  Reg#(Bool)     isIntra_d();
  mkReg#(False)  the_isIntra_d(isIntra_d);

  Reg#(Bool)     video_packet_header_detected();
  mkReg#(False)  the_video_packet_header_detected(video_packet_header_detected);

  Reg#(Bool)     start_code_detected();
  mkReg#(False)  the_start_code_detected(start_code_detected);

  Bool   isIntra = (mbtype == 3) || (mbtype == 4);
  Bit#(1) isInter = isIntra ? 0 : 1;

  Reg#(Bit#(2))  cbpc();
  mkReg#(0)      the_cbpc(cbpc);

  Reg#(Bit#(1))  ac_pred_flag();
  mkReg#(0)      the_ac_pred_flag(ac_pred_flag);

  Reg#(Bit#(4))  cbpy();
  mkReg#(0)      the_cbpy(cbpy);

  Reg#(Bit#(2))  mv_count();
  mkReg#(0)      the_mv_count(mv_count);

  Reg#(Bit#(3))  update_cnt();
  mkReg#(0)      the_update_cnt(update_cnt);

  Reg#(Bool)     mvp_done();
  mkReg#(False)  the_mvp_done(mvp_done);

  RegFile#(Bit#(2),Bit#(12)) horizontal_mv_data();
  mkRegFile#(0,3)  the_horizontal_mv_data(horizontal_mv_data);

  RegFile#(Bit#(2),Bit#(6)) horizontal_mv_residual();
  mkRegFile#(0,3)  the_horizontal_mv_residual(horizontal_mv_residual);

  RegFile#(Bit#(2),Bit#(12)) vertical_mv_data();
  mkRegFile#(0,3)  the_vertical_mv_data(vertical_mv_data);

  RegFile#(Bit#(2),Bit#(6)) vertical_mv_residual();
  mkRegFile#(0,3)  the_vertical_mv_residual(vertical_mv_residual);

  Reg#(Bit#(48)) mvx();
  mkReg#(0)      the_mvx(mvx);

  Reg#(Bit#(48)) mvy();
  mkReg#(0)      the_mvy(mvy);

  Reg#(Bit#(3))  blk_cnt();
  mkReg#(0)      the_blk_cnt(blk_cnt);

  Reg#(Bit#(5))  mb_num_x();
  mkReg#(0)      the_mb_num_x(mb_num_x);

  Reg#(Bit#(5))  mb_num_y();
  mkReg#(0)      the_mb_num_y(mb_num_y);

  Reg#(Bit#(9))  macroblock_number();
  mkReg#(0)      the_macroblock_number(macroblock_number);

  Reg#(Bit#(3))  vop_blk_num();
  mkReg#(0)      the_vop_blk_num(vop_blk_num);

  Reg#(Bit#(5))  vop_mb_num_x();
  mkReg#(0)      the_vop_mb_num_x(vop_mb_num_x);

  Reg#(Bit#(5))  vop_mb_num_y();
  mkReg#(0)      the_vop_mb_num_y(vop_mb_num_y);

  Reg#(Bool)     last();
  mkReg#(False)  the_last(last);

  Reg#(Bit#(6))  dct_coeff_cnt();
  mkReg#(0)      the_dct_coeff_cnt(dct_coeff_cnt);

  Reg#(Bit#(6))  cbuff_addr();
  mkReg#(0)      the_cbuff_addr(cbuff_addr);

  Reg#(Bit#(6))  cbuff_addr_d();
  mkReg#(0)      the_cbuff_addr_d(cbuff_addr_d);

  Reg#(Bit#(8))  intra_dc_coefficient();
  mkReg#(0)      the_intra_dc_coefficient(intra_dc_coefficient);

  Reg#(Bit#(4))  dct_dc_size_luma();
  mkReg#(0)      the_dct_dc_size_luma(dct_dc_size_luma);

  Reg#(Bit#(12)) differential_dc();
  mkReg#(0)      the_differential_dc(differential_dc);

  Reg#(Bit#(4))  dct_dc_size_chroma();
  mkReg#(0)      the_dct_dc_size_chroma(dct_dc_size_chroma);

  Reg#(Bit#(6))  run();
  mkReg#(0)      the_run(run);

  Reg#(Bit#(12)) level();
  mkReg#(0)      the_level(level);

  //Reg#(Bit#(1))  sign();
  //mkReg#(0)      the_sign(sign);

  RegFile#(Bit#(3),Bit#(7)) vlc_intra_table_1();
  mkRegFileLoad#("VLC_TABLE/usable_vlc_intra_table1.txt",0,7)  the_vlc_intra_table_1(vlc_intra_table_1);

  RegFile#(Bit#(4),Bit#(12)) vlc_intra_table_2();
  mkRegFileLoad#("VLC_TABLE/usable_vlc_intra_table2.txt",0,15)  the_vlc_intra_table_2(vlc_intra_table_2);

  RegFile#(Bit#(4),Bit#(12)) vlc_intra_table_3();
  mkRegFileLoad#("VLC_TABLE/usable_vlc_intra_table3.txt",0,15)  the_vlc_intra_table_3(vlc_intra_table_3);

  RegFile#(Bit#(5),Bit#(14)) vlc_intra_table_4();
  mkRegFileLoad#("VLC_TABLE/usable_vlc_intra_table4.txt",0,31)  the_vlc_intra_table_4(vlc_intra_table_4);

  RegFile#(Bit#(5),Bit#(14)) vlc_intra_table_5();
  mkRegFileLoad#("VLC_TABLE/usable_vlc_intra_table5.txt",0,31)  the_vlc_intra_table_5(vlc_intra_table_5);

  RegFile#(Bit#(5),Bit#(15)) vlc_intra_table_6();
  mkRegFileLoad#("VLC_TABLE/usable_vlc_intra_table6.txt",0,31)  the_vlc_intra_table_6(vlc_intra_table_6);

  RegFile#(Bit#(3),Bit#(13)) vlc_intra_table_7();
  mkRegFileLoad#("VLC_TABLE/usable_vlc_intra_table7.txt",0,7)  the_vlc_intra_table_7(vlc_intra_table_7);

  RegFile#(Bit#(2),Bit#(12)) vlc_intra_table_8();
  mkRegFileLoad#("VLC_TABLE/usable_vlc_intra_table8.txt",0,3)  the_vlc_intra_table_8(vlc_intra_table_8);

  RegFile#(Bit#(2),Bit#(13)) vlc_intra_table_9();
  mkRegFileLoad#("VLC_TABLE/usable_vlc_intra_table9.txt",0,3)  the_vlc_intra_table_9(vlc_intra_table_9);

  RegFile#(Bit#(3),Bit#(7)) vlc_inter_table_1();
  mkRegFileLoad#("VLC_TABLE/usable_vlc_inter_table1.txt",0,7)  the_vlc_inter_table_1(vlc_inter_table_1);

  RegFile#(Bit#(4),Bit#(10)) vlc_inter_table_2();
  mkRegFileLoad#("VLC_TABLE/usable_vlc_inter_table2.txt",0,15)  the_vlc_inter_table_2(vlc_inter_table_2);

  RegFile#(Bit#(4),Bit#(11)) vlc_inter_table_3();
  mkRegFileLoad#("VLC_TABLE/usable_vlc_inter_table3.txt",0,15)  the_vlc_inter_table_3(vlc_inter_table_3);

  RegFile#(Bit#(5),Bit#(12)) vlc_inter_table_4();
  mkRegFileLoad#("VLC_TABLE/usable_vlc_inter_table4.txt",0,31)  the_vlc_inter_table_4(vlc_inter_table_4);

  RegFile#(Bit#(5),Bit#(13)) vlc_inter_table_5();
  mkRegFileLoad#("VLC_TABLE/usable_vlc_inter_table5.txt",0,31)  the_vlc_inter_table_5(vlc_inter_table_5);

  RegFile#(Bit#(5),Bit#(14)) vlc_inter_table_6();
  mkRegFileLoad#("VLC_TABLE/usable_vlc_inter_table6.txt",0,31)  the_vlc_inter_table_6(vlc_inter_table_6);

  RegFile#(Bit#(3),Bit#(10)) vlc_inter_table_7();
  mkRegFileLoad#("VLC_TABLE/usable_vlc_inter_table7.txt",0,7)  the_vlc_inter_table_7(vlc_inter_table_7);

  RegFile#(Bit#(2),Bit#(9)) vlc_inter_table_8();
  mkRegFileLoad#("VLC_TABLE/usable_vlc_inter_table8.txt",0,3)  the_vlc_inter_table_8(vlc_inter_table_8);

  RegFile#(Bit#(2),Bit#(8)) vlc_inter_table_9();
  mkRegFileLoad#("VLC_TABLE/usable_vlc_inter_table9.txt",0,3)  the_vlc_inter_table_9(vlc_inter_table_9);

  Bool pattern_code = ((blk_cnt == 0) && (cbpy[3] == 1)) ||
                      ((blk_cnt == 1) && (cbpy[2] == 1)) ||
                      ((blk_cnt == 2) && (cbpy[1] == 1)) ||
                      ((blk_cnt == 3) && (cbpy[0] == 1)) ||
                      ((blk_cnt == 4) && (cbpc[1] == 1)) ||
                      ((blk_cnt == 5) && (cbpc[0] == 1)) ;

  Reg#(Bool)     pattern_code_d();
  mkReg#(False)  the_pattern_code_d(pattern_code_d);

  Reg#(Bool)     pattern_code_2d();
  mkReg#(False)  the_pattern_code_2d(pattern_code_2d);

  Bit#(5)  tmp_vop_fcode_forward = zeroExtend(vop_fcode_forward) -1 ;
  Bit#(5)  tmp_vop_fcode_forward1 = zeroExtend(vop_fcode_forward)  + 1;

  Reg#(Bool)     not_first_time();
  mkReg#(False)  the_not_first_time(not_first_time);

  Reg#(Bool)     acpred_flag();
  mkReg#(False)  the_acpred_flag(acpred_flag);

  Reg#(Bool)     acDCPredRequired();
  mkReg#(False)  the_acDCPredRequired(acDCPredRequired);

  Reg#(Bool)     acDCPredDone();
  mkReg#(False)  the_acDCPredDone(acDCPredDone);

  Reg#(Bit#(16)) dc_coeff();
  mkReg#(0)      the_dc_coeff(dc_coeff);

  Reg#(Bit#(12)) ac_coeff();
  mkReg#(0)      the_ac_coeff(ac_coeff);

  Reg#(Bit#(12)) predicted_address();
  mkReg#(0)  the_predicted_address(predicted_address);

  Reg#(Bit#(12)) acdcpredbuf_cur_addr();
  mkReg#(0)  the_acdcpredbuf_cur_addr(acdcpredbuf_cur_addr);

  Reg#(Bit#(12)) tmp_ac_addr();
  mkReg#(0)  the_tmp_ac_addr(tmp_ac_addr);

  Reg#(Bit#(4))  acdcpred_cnt();
  mkReg#(0)      the_acdcpred_cnt(acdcpred_cnt);

  Reg#(Bit#(6))  tmp_buf_addr();
  mkReg#(0)      the_tmp_buf_addr(tmp_buf_addr);

  Reg#(Bool)     vertical_dir();
  mkReg#(False)  the_vertical_dir(vertical_dir);

  Reg#(Bit#(1)) header_extension_code();
  mkReg#(0)  the_header_extension_code(header_extension_code);

/*
  Reg#(Bool)     clear_signal_sent();
  mkReg#(False)  the_clear_signal_sent(clear_signal_sent);
*/

  Bit#(12) tmp_mb_num_y = zeroExtend(mb_num_y);
  Bit#(12) tmp_mb_num_x = zeroExtend(mb_num_x);
  Bit#(12) tmp_mb_width = zeroExtend(mb_width);
  Bit#(12) tmp_vop_mb_num_y = zeroExtend(vop_mb_num_y);
  Bit#(12) tmp_vop_mb_num_x = zeroExtend(vop_mb_num_x);
  Bit#(12) byteOffset = (blk_cnt < 4) ? 0 :
                         (blk_cnt == 4) ? ((mb_width == 11) ? 12'd1320 : 12'd2640) :
						                  ((mb_width == 11) ? 12'd1650 : 12'd3300) ;
  Bit#(12) address = (blk_cnt < 4) ? 
                     (zeroExtend(tmp_vop_mb_num_y[0]) * 2*tmp_mb_width  + tmp_vop_mb_num_x)*12'd30 : 
                     (zeroExtend(tmp_vop_mb_num_y[0]) * tmp_mb_width  + tmp_vop_mb_num_x)*12'd15 ; 
  Bit#(12) address_luma = (blk_cnt < 2) ? (address + zeroExtend(blk_cnt)*12'd15) : 
                           (address + (2*tmp_mb_width + zeroExtend(blk_cnt[0]))*12'd15);
  Bit#(12) address_chroma = address + byteOffset;
  Bit#(12) current_address = (blk_cnt < 4) ? address_luma : address_chroma;

  Bit#(10) dc_scaler =  func_get_dc_scaler(short_video_header,blk_cnt,running_QP[9:0]);

  Bit#(6)  tmp_cbuff_addr = (isIntra && (ac_pred_flag == 1) && acpred_flag) ? 
	                             ((vertical_dir) ?  
								    inverse_scan_alternate_vertical(dct_coeff_cnt) :
	                                inverse_scan_alternate_horizontal(dct_coeff_cnt)) :
	                           inverse_scan_zigzag(dct_coeff_cnt);

  Bit#(8) weighting_matrix = isIntra ? 
	         intra_quant_mat.sub(tmp_cbuff_addr) : 
			 non_intra_quant_mat.sub(tmp_cbuff_addr);

  Reg#(Bit#(12)) cbuff_data();
  mkReg#(0)      the_cbuff_data(cbuff_data);

  Bit#(13) macroblock_num_width = ((video_object_layer_height + 15) >> 4 ) * 
                                 ((video_object_layer_width + 15) >> 4 );
  Bit#(5)  mb_bit_width = decode_length(macroblock_num_width);
  Bit#(9)  mbNum = zeroExtend(mb_width)*zeroExtend(mb_num_y) + zeroExtend(mb_num_x);

  Bit#(8) mv_offset_addr = (4*zeroExtend(vop_mb_num_y[0])*mb_width[7:0])  + 
                           (2*zeroExtend(vop_mb_num_x)) + 
						   zeroExtend(update_cnt[0]);
  Bit#(8) mv_addr = (update_cnt < 2) ?  mv_offset_addr : (mv_offset_addr + mb_width[7:0]*2);

  Reg#(Mbheadertype)            mbhdrdata_reg();
  mkReg#(tuple7(0,0,0,0,0,0,0)) t_mbhdrdata_reg(mbhdrdata_reg);

  Reg#(Bool)     vop_start_code_detected();
  mkReg#(False)  the_vop_start_code_detected(vop_start_code_detected);

  Reg#(Bit#(1))     disable_mb_done_reg();
  mkReg#(0)  the_disable_mb_done_reg(disable_mb_done_reg);

// ###############################################
// Instantiations of sub-block are done here
  ByteAlign_IFC  byteAlign <- mkByteAlign;
  CBuffer_IFC    blkBuffer <- mkCBuffer;
  Inverse_Quantization_IFC inverse_quant <- mkInverse_quantized;
  Division_IFC division <- mkDiv;
  RegFile#(Bit#(12),Maybe#(Bit#(24))) acdcPredBuffer();
  mkRegFile #(0,3960) the_acdcPredBuffer (acdcPredBuffer);
  FLCDecode_IFC flc <- mkFLCDecode;
  FIFOF#(Mbheadertype) mbheaderfifo <- mkSizedFIFOF(398); // max mbs in simple profile
  RegFile#(Bit#(8),Maybe#(Bit#(12))) mvPredBuffer_x();
  mkRegFile #(0,175) the_mvPredBuffer_x(mvPredBuffer_x);
  RegFile#(Bit#(8),Maybe#(Bit#(12))) mvPredBuffer_y();
  mkRegFile #(0,175) the_mvPredBuffer_y(mvPredBuffer_y);
  MVarith_IFC  mvarith <- mkMVarith;

   // ###############################################
   // try to get ride of all the invalid reads - just looks bad
   function Maybe#(Bit#(24)) acdcPredBuffer_sub( Bit#(12) addr );
      if (addr == -1) return Invalid;
      else            return acdcPredBuffer.sub(addr);
   endfunction
   
// *************************************************
// Start of block0
// *************************************************
function Rules create_block0 ();
 Rules r = rules
  rule write_PSState ((host_strobe.wget == Just(1)) &&
                      (host_select.wget == Just(0)) &&
					  (host_address.wget == Just(0))&&
					  (sysState == IDLE));
      if (host_datain.wget == Just(1))
	 begin
	    sysState <= START;	
            vd_rd_reg <= 1'b1;
	    $display("START detected");
	 end
  endrule

  rule dequeheaderfifo (rdmv.wget == Just(1));
    $display("sending mb header ");
    mbheaderfifo.deq;
    mbhdrdata_reg <= mbheaderfifo.first;
  endrule

  //rule send_header_out (mbheaderfifo.notEmpty == True);
  //endrule

endrules;
return r;
endfunction
// *************************************************
// End of block0
// *************************************************

// *************************************************
// Start of block1
// *************************************************
function Rules create_block1 ();
 Rules r = rules
  rule filldatabuffer ((sysState == START ) && (vd_valid.wget == Just(1)));
    start_code_reg <= {start_code_reg[31:0],unJust(vd_data.wget)};
  endrule

  rule detect_video_object_start_code (videoSt == IDLE);
    Tuple3#(Bool,Bit#(4),Bit#(5)) start_code = detvideoobjectstartcode(start_code_reg);
	if (tpl_1(start_code))
	  begin
	    byte_align_pos <= tpl_2(start_code);
	    video_object_number <= tpl_3(start_code);
		videoSt        <= VIDEO_OBJECT_LAYER0;
		sysState       <= WAIT;
        vd_rd_reg <= 1'b0;
		$display("start code detected byte_align_pos %d ",byte_align_pos);
	  end
	else
        vd_rd_reg <= 1'b1;
  endrule

  rule detect_video_object_layer_start_code0 (videoSt == VIDEO_OBJECT_LAYER0);
    start_code_reg <= byteAlign.flushdata(byte_align_pos,start_code_reg);
	$display("start code reg %h ",start_code_reg);
	sysState <= START;
	videoSt <= VIDEO_OBJECT_LAYER1;
	byte_offset <= zeroExtend(byte_align_pos) ;
    vd_rd_reg <= 1'b1;
  endrule

  rule detect_video_object_layer_start_code1 ((videoSt == VIDEO_OBJECT_LAYER1) &&
                                              (cnt != 4) );
    Tuple3#(Bool,Bit#(4),Bit#(4)) start_code = detvideoobjectlayerstartcode(start_code_reg);
	if (tpl_1(start_code))
	  begin
	    byte_align_pos <= tpl_2(start_code);
	    vol_number     <= tpl_3(start_code);
		//videoSt        <= VIDEO_OBJECT_LAYER1_1;
		videoSt        <= VIDEO_OBJECT_LAYER2;
		sysState       <= WAIT;
        vd_rd_reg <= 1'b0;
	    byte_offset <= zeroExtend(tpl_2(start_code)) + 8;
		$display("video object layer start code detected");
	  end
	cnt <= cnt + 1;
	$display("detect_video_object_layer_start_code1 start code reg %h ",start_code_reg);
  endrule

  rule detect_video_object_layer_start_code2 (videoSt == VIDEO_OBJECT_LAYER2);
	 Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	 random_accessible_vol <= tmp[0];
	 byte_boundary <= byte_boundary + 1;
	 if (byte_offset < 9)
	  begin
	    sysState <= START;
	    byte_offset <= byte_offset + 8 - 1;
        vd_rd_reg <= 1'b1;
	    videoSt        <= VIDEO_OBJECT_LAYER2_0;
	  end
    else
	  begin
	    sysState <= WAIT;
	    byte_offset <= byte_offset - 1;
        vd_rd_reg <= 1'b0;
	    videoSt        <= VIDEO_OBJECT_LAYER2_1;
	  end

	 $display("I'm in layer2 tmp = %h byte_offset = %d",tmp,byte_offset);
	 $display("detect_video_object_layer_start_code2 start code reg %h ",start_code_reg);
  endrule

  rule wait_1_cycle0 ((videoSt == VIDEO_OBJECT_LAYER2_0) && (vd_valid.wget == Just(1))) ;
	 videoSt <= VIDEO_OBJECT_LAYER2_1;
	 $display("wait_1_cycle0 start code reg %h ",start_code_reg);
  endrule

  rule detect_video_object_layer_start_code2_1 (videoSt == VIDEO_OBJECT_LAYER2_1);
	 Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	 video_object_type_indication <= zeroExtend(tmp[7:0]);
	 //byte_boundary <= byte_boundary + 8; No point adding 8 as already on byte boundary
	 if (byte_offset < 9)
	   begin
	    byte_offset <= byte_offset ;
		if (sysState == WAIT)
	      videoSt <= VIDEO_OBJECT_LAYER2_1_0;
		else
	      videoSt <= VIDEO_OBJECT_LAYER3;
	    sysState <= START;
        vd_rd_reg <= 1'b1;
	   end
	 else
	   begin
	    sysState <= WAIT;
		if (sysState == WAIT)
	      byte_offset <= byte_offset - 8;
		else
	      byte_offset <= byte_offset ;
	    videoSt <= VIDEO_OBJECT_LAYER3;
        vd_rd_reg <= 1'b0;
	   end
	 $display("I'm in layer21 tmp = %h byte_offset = %d",tmp,byte_offset);
	 $display("detect_video_object_layer_start_code2_1 start code reg %h ",start_code_reg);
  endrule

  rule wait_1_cycle1 ((videoSt == VIDEO_OBJECT_LAYER2_1_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER3; 
	$display("wait_1_cycle0 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code3 (videoSt == VIDEO_OBJECT_LAYER3);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	byte_boundary <= byte_boundary + 1;
    is_object_layer_identifier <= tmp[0]; 
    sysState <= WAIT; 
    vd_rd_reg <= 1'b0;
    videoSt  <= VIDEO_OBJECT_LAYER3_0; 
    byte_offset <= byte_offset - 1;
    $display("I'm in layer3 tmp = %h byte_offset = %d",tmp,byte_offset);
    $display("detect_video_object_layer_start_code3 start code reg %h",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code3_0 (videoSt == VIDEO_OBJECT_LAYER3_0); 
    if (is_object_layer_identifier == 1'b1) // IS_OBJECT_LAYER_IDETIFIER IS TRUE 
	  begin 
	    if (byte_offset < 7) 
		  begin 
		    if (sysState == WAIT) 
			  videoSt  <= VIDEO_OBJECT_LAYER3_0_1; 
			else 
			  videoSt  <= VIDEO_OBJECT_LAYER3_1; 
			sysState <= START; 
			vd_rd_reg <= 1'b1; 
			byte_offset <= byte_offset + 8; 
		  end 
		else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset + 8; 
		      end 
		    else 
		      byte_offset <= byte_offset ;
            videoSt  <= VIDEO_OBJECT_LAYER3_1; 
          end 
	  end 
    else 
	  begin 
	    if (byte_offset < 4) 
		  begin 
		    if (sysState == WAIT) 
			  videoSt  <= VIDEO_OBJECT_LAYER3_0_2; 
			else 
			  videoSt  <= VIDEO_OBJECT_LAYER3_2; 
			sysState <= START; 
			vd_rd_reg <= 1'b1; 
			byte_offset <= byte_offset + 8; 
		  end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset + 8; 
		      end 
		    else 
		      byte_offset <= byte_offset ;
            videoSt  <= VIDEO_OBJECT_LAYER3_2; 
          end 
	  end 
	$display("I'm in layer3_0 byte_offset = %d",byte_offset); 
	$display("detect_video_object_layer_start_code3_0 start_code_reg %h ",start_code_reg); 
  endrule

  rule wait_1_cycle2 ((videoSt == VIDEO_OBJECT_LAYER3_0_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER3_1; 
	$display("wait_1_cycle2 start code reg %h ",start_code_reg); 
  endrule

  rule wait_1_cycle3 ((videoSt == VIDEO_OBJECT_LAYER3_0_2) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER3_2; 
	$display("wait_1_cycle3 start code reg %h ",start_code_reg); 
  endrule

  rule is_object_layer_idetifier_true (videoSt == VIDEO_OBJECT_LAYER3_1);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,7);
    video_object_layer_verid <= tmp[6:3]; 
	video_object_layer_priority <= tmp[2:0]; 
	byte_boundary <= byte_boundary + 7;
	if (byte_offset < 11) 
	  begin 
	    if (sysState == WAIT) 
		  videoSt  <= VIDEO_OBJECT_LAYER3_0_2; 
		else 
		  videoSt  <= VIDEO_OBJECT_LAYER3_2; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset    <= byte_offset + 8 - 7; 
	  end 
	else
      begin 
	    if (sysState == WAIT) 
		  begin 
		    byte_offset <= byte_offset - 7; 
			videoSt  <= VIDEO_OBJECT_LAYER3_2; 
		  end 
		else 
		  begin 
		    byte_offset <= byte_offset + 8 - 7;
            videoSt  <= VIDEO_OBJECT_LAYER3_2; 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		  end
      end 
    $display("I'm in is_object_layer_idetifier_true tmp = %h byte_offset = %d",tmp,byte_offset); 
	$display("detect_video_object_layer_start_code3_1 start_code_reg %h ",start_code_reg); 
  endrule

  rule is_object_layer_idetifier_false (videoSt == VIDEO_OBJECT_LAYER3_2);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,4); 
	aspect_ratio_info <= tmp[3:0]; 
	byte_boundary <= byte_boundary + 4;
    if (tmp[3:0] == eXTENDED_PAR) 
	  begin 
	    if (byte_offset < 12) 
		  begin 
		    if (sysState == WAIT) 
			  videoSt  <= VIDEO_OBJECT_LAYER4_0_1; 
			else 
			  videoSt  <= VIDEO_OBJECT_LAYER4_1; 
			byte_offset <= byte_offset + 8 - 4; 
			sysState <= START; 
			vd_rd_reg <= 1'b1; 
		  end 
		else
		  begin 
		    if (sysState == START)
			  begin
			    vd_rd_reg <= 1'b0; 
			    byte_offset <= byte_offset + 8 -4 ; 
			    sysState <= WAIT; 
			  end
			 else
			    byte_offset <= byte_offset - 4 ; 
			videoSt  <= VIDEO_OBJECT_LAYER4_1; 
		  end 
	  end 
    else 
	  begin
	    if (byte_offset < 5) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER4_1_1; 
		    else 
		      videoSt  <= VIDEO_OBJECT_LAYER4_2; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset + 8 - 4; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 - 4; 
			    sysState <= WAIT; 
		      end 
		    else 
		      byte_offset <= byte_offset - 4;
            videoSt  <= VIDEO_OBJECT_LAYER4_2; 
	       end
	    end 
    $display("I'm in is_object_layer_idetifier_false tmp = %h byte_offset = %d",tmp,byte_offset); 
	$display("detect_video_object_layer_start_code3_2 %h ",start_code_reg); 
  endrule

  rule wait_1_cycle4 ((videoSt == VIDEO_OBJECT_LAYER4_0_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER4_1; 
	$display("wait_1_cycle4 start code reg %h ",start_code_reg); 
  endrule

  rule wait_1_cycle5 ((videoSt == VIDEO_OBJECT_LAYER4_1_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER4_2; 
	$display("wait_1_cycle5 start code reg %h ",start_code_reg); 
  endrule
  
  rule detect_video_object_layer_start_code4_1 (videoSt == VIDEO_OBJECT_LAYER4_1);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	par_width <= tmp[7:0];
	//if (byte_offset < 16) 
	  //begin 
	    if (sysState == WAIT) 
		  videoSt  <= VIDEO_OBJECT_LAYER4_1_2; 
		else 
		  videoSt  <= VIDEO_OBJECT_LAYER4_1_3; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset    <= byte_offset ; 
	  //end 
	  /*
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset ;
		  end 
		else 
		  byte_offset <= byte_offset - 8; 
        videoSt  <= VIDEO_OBJECT_LAYER4_1_3; 
      end 
	  */
  endrule

  rule wait_1_cycle6 ((videoSt == VIDEO_OBJECT_LAYER4_1_2) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER4_1_3; 
	$display("wait_1_cycle6 start code reg %h ",start_code_reg); 
  endrule
  

  rule detect_video_object_layer_start_code4_1_3 (videoSt == VIDEO_OBJECT_LAYER4_1_3);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	par_heigth <= tmp[7:0];
	if (byte_offset < 9) 
	  begin 
	    if (sysState == WAIT) 
		  videoSt  <= VIDEO_OBJECT_LAYER4_2_1; 
		else 
		  videoSt  <= VIDEO_OBJECT_LAYER4_2; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset    <= byte_offset ; 
	  end 
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset ;
		  end 
		else 
		  byte_offset <= byte_offset - 8; 
        videoSt  <= VIDEO_OBJECT_LAYER4_2; 
      end 
  endrule

  rule wait_1_cycle7 ((videoSt == VIDEO_OBJECT_LAYER4_2_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER4_2; 
	$display("wait_1_cycle7 start code reg %h ",start_code_reg); 
  endrule
  

  rule detect_video_object_layer_start_code4 (videoSt == VIDEO_OBJECT_LAYER4_2);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
    vol_control_parameters <= tmp[0]; 
	byte_boundary <= byte_boundary + 1;
    if (tmp[0] == 1'b1) 
	  begin 
	    if (byte_offset < 5) 
		  begin 
		    if (sysState == WAIT) 
			  videoSt  <= VIDEO_OBJECT_LAYER5_0_1; 
			else 
			  videoSt  <= VIDEO_OBJECT_LAYER5_1; 
			byte_offset <= byte_offset + 8 - 1; 
			sysState <= START; 
			vd_rd_reg <= 1'b1; 
		  end 
		else
		  begin 
		    if (sysState == START)
			  begin
			    vd_rd_reg <= 1'b0; 
			    byte_offset <= byte_offset + 8 -1 ; 
			    sysState <= WAIT; 
			  end
			 else
			    byte_offset <= byte_offset - 1 ; 
			videoSt  <= VIDEO_OBJECT_LAYER5_1; 
		  end 
	  end 
    else 
	  begin
	    if (byte_offset < 3) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER5_1_1; 
		    else 
		      videoSt  <= VIDEO_OBJECT_LAYER5_2; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset + 8 - 1; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 - 1; 
			    sysState <= WAIT; 
		      end 
		    else 
		      byte_offset <= byte_offset - 1;
            videoSt  <= VIDEO_OBJECT_LAYER5_2; 
	       end
	    end 
    $display("I'm in layer4 tmp = %h byte_offset = %d",tmp,byte_offset);
    $display("detect_video_object_layer_start_code4_2 start_code_reg %h ",start_code_reg); 
  endrule

  rule wait_1_cycle8 ((videoSt == VIDEO_OBJECT_LAYER5_0_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER5_1; 
	$display("wait_1_cycle8 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code5_1 (videoSt == VIDEO_OBJECT_LAYER5_1);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,4);
	chroma_format <= tmp[3:2];
	low_delay <= tmp[1];
	vbv_parameters <= tmp[0];
	byte_boundary <= byte_boundary + 4;
	if (tmp[0] == 1)  // VBV_PARAMETERS is SET
	  begin
	    if (byte_offset < 12) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER5_1_1_1; 
		    else 
		      videoSt  <= VIDEO_OBJECT_LAYER5_1_2; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 -4; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 -4;
		      end 
		    else 
		      byte_offset <= byte_offset - 4; 
            videoSt  <= VIDEO_OBJECT_LAYER5_1_2; 
          end 
	  end
	else
	  begin
	    if (byte_offset < 6) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER5_2_1; 
		    else 
		      videoSt  <= VIDEO_OBJECT_LAYER5_2; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 -4; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 -4;
		      end 
		    else 
		      byte_offset <= byte_offset - 4; 
            videoSt  <= VIDEO_OBJECT_LAYER5_2; 
          end 
	  end
  endrule

  rule wait_1_cycle9 ((videoSt == VIDEO_OBJECT_LAYER5_1_1_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER5_1_2; 
	$display("wait_1_cycle8 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code5_1_2 (videoSt == VIDEO_OBJECT_LAYER5_1_2);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	first_half_bit_rate <= zeroExtend(tmp[7:0]);
	if (sysState == WAIT) 
	  videoSt  <= VIDEO_OBJECT_LAYER5_1_2_1; 
	else 
	  videoSt  <= VIDEO_OBJECT_LAYER5_1_3; 
	sysState <= START; 
	vd_rd_reg <= 1'b1; 
	byte_offset <= byte_offset ; 
  endrule

  rule wait_1_cycle10 ((videoSt == VIDEO_OBJECT_LAYER5_1_2_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER5_1_3; 
	$display("wait_1_cycle10 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code5_1_3 (videoSt == VIDEO_OBJECT_LAYER5_1_3);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	first_half_bit_rate <= {first_half_bit_rate[7:0],tmp[6:0]};
	marker_bit <= tmp[0];
	videoSt  <= VIDEO_OBJECT_LAYER5_1_4; 
	byte_offset <= byte_offset ; 
  endrule

  rule detect_video_object_layer_start_code5_1_4 (videoSt == VIDEO_OBJECT_LAYER5_1_4);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	latter_half_bit_rate <= zeroExtend(tmp[7:0]);
	videoSt  <= VIDEO_OBJECT_LAYER5_1_5; 
	byte_offset <= byte_offset ; 
  endrule

  rule detect_video_object_layer_start_code5_1_5 (videoSt == VIDEO_OBJECT_LAYER5_1_5);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	latter_half_bit_rate <= {latter_half_bit_rate[7:0],tmp[6:0]};
	marker_bit <= tmp[0];
	videoSt  <= VIDEO_OBJECT_LAYER5_1_6; 
	byte_offset <= byte_offset ; 
  endrule

  rule detect_video_object_layer_start_code5_1_6 (videoSt == VIDEO_OBJECT_LAYER5_1_6);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	first_half_vbv_buffer_size <= zeroExtend(tmp[7:0]);
	videoSt  <= VIDEO_OBJECT_LAYER5_1_7; 
	byte_offset <= byte_offset ; 
  endrule

  rule detect_video_object_layer_start_code5_1_7 (videoSt == VIDEO_OBJECT_LAYER5_1_7);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	first_half_vbv_buffer_size <= {first_half_vbv_buffer_size[7:0],tmp[6:0]};
	marker_bit <= tmp[0];
	videoSt  <= VIDEO_OBJECT_LAYER5_1_8; 
	byte_offset <= byte_offset ; 
  endrule

  rule detect_video_object_layer_start_code5_1_8 (videoSt == VIDEO_OBJECT_LAYER5_1_8);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	latter_half_vbv_buffer_size <= tmp[7:5];
	first_half_vbv_occupancy <= zeroExtend(tmp[4:0]);
	videoSt  <= VIDEO_OBJECT_LAYER5_1_9; 
	byte_offset <= byte_offset ; 
  endrule

  rule detect_video_object_layer_start_code5_1_9 (videoSt == VIDEO_OBJECT_LAYER5_1_9);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,7);
	first_half_vbv_occupancy <= {first_half_vbv_occupancy[4:0],tmp[6:1]};
	marker_bit <= tmp[0];
	videoSt  <= VIDEO_OBJECT_LAYER5_1_10; 
	byte_offset <= byte_offset + 1; 
	byte_boundary <= byte_boundary + 7;
  endrule

  rule detect_video_object_layer_start_code5_1_10 (videoSt == VIDEO_OBJECT_LAYER5_1_10);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	latter_half_vbv_occupancy <= zeroExtend(tmp[7:0]);
	videoSt  <= VIDEO_OBJECT_LAYER5_1_11; 
	byte_offset <= byte_offset ; 
  endrule

  rule detect_video_object_layer_start_code5_1_11 (videoSt == VIDEO_OBJECT_LAYER5_1_11);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	latter_half_vbv_occupancy <= {latter_half_vbv_occupancy[7:0],tmp[7:1]} ;
	marker_bit <= tmp[0];
	videoSt  <= VIDEO_OBJECT_LAYER5_2; 
	byte_offset <= byte_offset ; 
  endrule

  rule wait_1_cycle11 ((videoSt == VIDEO_OBJECT_LAYER5_2_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER5_2; 
	$display("wait_1_cycle11 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code5_2 (videoSt == VIDEO_OBJECT_LAYER5_2);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,2);
	video_object_layer_shape <= tmp[1:0];
	byte_boundary <= byte_boundary + 2;
	if ((tmp[1:0] == gRAYSCALE) && (video_object_layer_verid != 4'b0001))
	  begin
	    if (byte_offset < 6) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER5_2_2_0; 
		    else 
		      videoSt  <= VIDEO_OBJECT_LAYER5_2_2; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 -2; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 - 2;
		      end 
		    else 
		      byte_offset <= byte_offset - 2; 
            videoSt  <= VIDEO_OBJECT_LAYER5_2_2; 
          end 
	  end
	else
	  begin
	    if (byte_offset < 3) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER5_3_1; 
		    else 
		      videoSt  <= VIDEO_OBJECT_LAYER5_3; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 -2; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 - 2;
		      end 
		    else 
		      byte_offset <= byte_offset - 2; 
            videoSt  <= VIDEO_OBJECT_LAYER5_3; 
          end 
	  end
  endrule

  rule wait_1_cycle12 ((videoSt == VIDEO_OBJECT_LAYER5_2_2_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER5_2_2; 
	$display("wait_1_cycle12 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code5_2_2 (videoSt == VIDEO_OBJECT_LAYER5_2_2);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,4);
	video_object_layer_shape_extension <= tmp[3:0];
	byte_boundary <= byte_boundary + 4;
	if (byte_offset < 5) 
	  begin 
	    if (sysState == WAIT) 
		  videoSt  <= VIDEO_OBJECT_LAYER5_3_1; 
		else 
		  videoSt  <= VIDEO_OBJECT_LAYER5_3; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset    <= byte_offset +8 -4; 
	  end 
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 - 4;
		  end 
		else 
		  byte_offset <= byte_offset - 4; 
        videoSt  <= VIDEO_OBJECT_LAYER5_3; 
      end 
  endrule

  rule wait_1_cycle13 ((videoSt == VIDEO_OBJECT_LAYER5_3_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER5_3; 
	$display("wait_1_cycle13 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code5_3 (videoSt == VIDEO_OBJECT_LAYER5_3);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	marker_bit <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (byte_offset < 9) 
	  begin 
	    if (sysState == WAIT) 
		  videoSt  <= VIDEO_OBJECT_LAYER5_4_1; 
		else 
		  videoSt  <= VIDEO_OBJECT_LAYER5_4; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset    <= byte_offset +8 -1; 
	  end 
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 - 1;
		  end 
		else 
		  byte_offset <= byte_offset - 1; 
        videoSt  <= VIDEO_OBJECT_LAYER5_4; 
      end 
  endrule

  rule wait_1_cycle14 ((videoSt == VIDEO_OBJECT_LAYER5_4_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER5_4; 
	$display("wait_1_cycle14 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code5_4 (videoSt == VIDEO_OBJECT_LAYER5_4);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	vop_time_increment_resolution <= zeroExtend(tmp[7:0]);
	if (sysState == WAIT) 
	  videoSt  <= VIDEO_OBJECT_LAYER5_5_1; 
    else 
	  videoSt  <= VIDEO_OBJECT_LAYER5_5; 
	sysState <= START; 
	vd_rd_reg <= 1'b1; 
	byte_offset    <= byte_offset ; 
  endrule

  rule wait_1_cycle15 ((videoSt == VIDEO_OBJECT_LAYER5_5_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER5_5; 
	$display("wait_1_cycle15 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code5_5 (videoSt == VIDEO_OBJECT_LAYER5_5);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	vop_time_increment_resolution <= {vop_time_increment_resolution[7:0],tmp[7:0]};
	videoSt  <= VIDEO_OBJECT_LAYER5_6; 
	byte_offset    <= byte_offset ; 
  endrule

  rule detect_video_object_layer_start_code5_6 (videoSt == VIDEO_OBJECT_LAYER5_6);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,2);
	tmp_vop_time_increment_resolution <= vop_time_increment_resolution;
	marker_bit <= tmp[1];
	fixed_vop_rate <= tmp[0];
	byte_boundary <= byte_boundary + 2;
	if (tmp[0] == 1'b1)  // FIXED VOP RATE is SET
      videoSt  <= VIDEO_OBJECT_LAYER5_6_0; 
	else
      videoSt  <= VIDEO_OBJECT_LAYER6; 
	if (sysState == START) 
	  begin 
		sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
		byte_offset <= byte_offset +8 - 2;
      end 
    else 
	  byte_offset <= byte_offset - 2; 
  endrule

  rule detect_video_object_layer_start_code5_6_0 (videoSt == VIDEO_OBJECT_LAYER5_6_0);
    if (tmp_vop_time_increment_resolution == 0)
	  begin
		if (byte_offset < fvti_num)
		  begin
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8 ; 
            videoSt  <= VIDEO_OBJECT_LAYER5_6_1_1; 
		  end
		else
          videoSt  <= VIDEO_OBJECT_LAYER5_6_1; 
	  end
	else
	  begin
       tmp_vop_time_increment_resolution  <= tmp_vop_time_increment_resolution >> 1;
	   fvti_num <= fvti_num + 1;
	  end
  endrule

  rule wait_1_cycle16 ((videoSt == VIDEO_OBJECT_LAYER5_6_1_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER5_6_1; 
	$display("wait_1_cycle16 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code5_6_1 (videoSt == VIDEO_OBJECT_LAYER5_6_1);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
    if (fvti_num > 8)
	  begin
		fvti_num <= fvti_num - 8;
	    fixed_vop_time_increment <= {fixed_vop_time_increment[7:0],tmp[7:0]};
	  end
	else
	  begin
        videoSt  <= VIDEO_OBJECT_LAYER5_6_2; 
	    if (sysState == START) 
	      begin 
		    sysState <= WAIT; 
		    vd_rd_reg <= 1'b0; 
	        byte_offset <= byte_offset + 8;
	      end 
	    else 
	      byte_offset <= byte_offset;
	  end
  endrule

  rule detect_video_object_layer_start_code5_6_2 (videoSt == VIDEO_OBJECT_LAYER5_6_2);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,fvti_num[3:0]);
	fixed_vop_time_increment <= byteAlign.bs(fixed_vop_time_increment,tmp,fvti_num[3:0]);
	byte_boundary <= byte_boundary + fvti_num[2:0];
	if (sysState == START) 
	  begin 
		sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
	    byte_offset <= byte_offset +8 - fvti_num;
	  end 
	else 
	  byte_offset <= byte_offset - fvti_num; 
    videoSt  <= VIDEO_OBJECT_LAYER6; 
  endrule

  rule detect_video_object_layer_start_code6 (videoSt == VIDEO_OBJECT_LAYER6);
    if (video_object_layer_shape != bINARY_ONLY)
      videoSt  <= VIDEO_OBJECT_LAYER7; 
	else
      videoSt  <= VIDEO_OBJECT_LAYER34;  // video_object_layer_shape is binary 
  endrule

  rule detect_video_object_layer_start_code7 (videoSt == VIDEO_OBJECT_LAYER7);
    if (video_object_layer_shape == rECTANGULAR)
	  begin
	    if (byte_offset < 1)
	      begin
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
	        byte_offset <= byte_offset +8 ;
            videoSt  <= VIDEO_OBJECT_LAYER9_1_0; 
	      end
	    else
          videoSt  <= VIDEO_OBJECT_LAYER9; 
	  end
	else
	  begin
	    if (byte_offset < 2)
	      begin
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
	        byte_offset <= byte_offset +8 ;
            videoSt  <= VIDEO_OBJECT_LAYER10_1_0; 
	      end
	    else
          videoSt  <= VIDEO_OBJECT_LAYER10; 
	  end
  endrule

  rule wait_1_cycle17 ((videoSt == VIDEO_OBJECT_LAYER9_1_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER9; 
	$display("wait_1_cycle17 start code reg %h ",start_code_reg); 
  endrule

  rule wait_1_cycle18 ((videoSt == VIDEO_OBJECT_LAYER10_1_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER10; 
	$display("wait_1_cycle18 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code9 (videoSt == VIDEO_OBJECT_LAYER9);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	marker_bit <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (byte_offset < 9) 
	  begin 
	    if (sysState == WAIT) 
		  videoSt  <= VIDEO_OBJECT_LAYER9_2_0; 
		else 
		  videoSt  <= VIDEO_OBJECT_LAYER9_2; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset    <= byte_offset +8 -1; 
	  end 
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 - 1;
		  end 
		else 
		  byte_offset <= byte_offset - 1; 
        videoSt  <= VIDEO_OBJECT_LAYER9_2; 
      end 
  endrule

  rule detect_video_object_layer_start_code9_2 (videoSt == VIDEO_OBJECT_LAYER9_2);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	video_object_layer_width <= zeroExtend(tmp[7:0]);
	if (byte_offset < 16)
	  begin
	    if (sysState == WAIT)
	      begin
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
            videoSt  <= VIDEO_OBJECT_LAYER9_3_1; 
	      end
	    else
          videoSt  <= VIDEO_OBJECT_LAYER9_3; 
	    byte_offset <= byte_offset ; 
	  end
	else
	  begin
	    if (sysState == START)
	      begin
		    sysState <= WAIT; 
		    vd_rd_reg <= 1'b0; 
	        byte_offset <= byte_offset ; 
	      end
	    else
	      byte_offset <= byte_offset -8  ; 
        videoSt  <= VIDEO_OBJECT_LAYER9_3; 
	  end
  endrule

  rule wait_1_cycle18_1 ((videoSt == VIDEO_OBJECT_LAYER9_3_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER9_3; 
	$display("wait_1_cycle18_1 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code9_3 (videoSt == VIDEO_OBJECT_LAYER9_3);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	video_object_layer_width <= {video_object_layer_width[7:0],tmp[7:3]};
	marker_bit <= tmp[2];
	video_object_layer_height <= zeroExtend(tmp[1:0]);
	if (byte_offset < 16)
	  begin
	    if (sysState == WAIT)
	      begin
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
            videoSt  <= VIDEO_OBJECT_LAYER9_4_1; 
	      end
	    else
          videoSt  <= VIDEO_OBJECT_LAYER9_4; 
	    byte_offset <= byte_offset ; 
	  end
	else
	  begin
	    if (sysState == START)
	      begin
		    sysState <= WAIT; 
		    vd_rd_reg <= 1'b0; 
	        byte_offset <= byte_offset ; 
	      end
	    else
	      byte_offset <= byte_offset -8  ; 
        videoSt  <= VIDEO_OBJECT_LAYER9_4; 
	  end
  endrule

  rule wait_1_cycle18_2 ((videoSt == VIDEO_OBJECT_LAYER9_4_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER9_4; 
	$display("wait_1_cycle18_2 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code9_4 (videoSt == VIDEO_OBJECT_LAYER9_4);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	video_object_layer_height <= zeroExtend({video_object_layer_height[1:0],tmp[7:0]});
	mb_width <= video_object_layer_width[12:4];
	if (byte_offset < 12) 
	  begin 
	    if (sysState == WAIT) 
		  videoSt  <= VIDEO_OBJECT_LAYER9_5_0; 
		else 
		  videoSt  <= VIDEO_OBJECT_LAYER9_5; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset    <= byte_offset ; 
	  end 
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset ;
		  end 
		else 
		  byte_offset <= byte_offset - 8; 
        videoSt  <= VIDEO_OBJECT_LAYER9_5; 
      end 
  endrule

  rule wait_1_cycle19_0 ((videoSt == VIDEO_OBJECT_LAYER9_5_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER9_5; 
	$display("wait_1_cycle19_0 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code9_5 (videoSt == VIDEO_OBJECT_LAYER9_5);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,4);
	video_object_layer_height <= {video_object_layer_height[9:0],tmp[3:1]};
	marker_bit <= tmp[0];
	byte_boundary <= byte_boundary + 4;
	 if (byte_offset < 6)
	   begin
	    byte_offset <= byte_offset + 8 - 4; 
		if (sysState == WAIT)
	      videoSt <= VIDEO_OBJECT_LAYER10_1_0;
		else
	      videoSt <= VIDEO_OBJECT_LAYER10;
	    sysState <= START;
        vd_rd_reg <= 1'b1;
	   end
	 else
	   begin
	    sysState <= WAIT;
		if (sysState == WAIT)
	      byte_offset <= byte_offset - 4;
		else
	      byte_offset <= byte_offset +8 -4;
	    videoSt <= VIDEO_OBJECT_LAYER10;
        vd_rd_reg <= 1'b0;
	   end
  endrule

  rule detect_video_object_layer_start_code10 (videoSt == VIDEO_OBJECT_LAYER10);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,2);
	mb_height <= video_object_layer_height[12:4];
	interlaced <= tmp[1];
	obmc_disable <= tmp[0];
	byte_boundary <= byte_boundary + 2;
	if (byte_offset < 3)
	   begin
	    byte_offset <= byte_offset + 8 - 2; 
		if (sysState == WAIT)
	      videoSt <= VIDEO_OBJECT_LAYER10_2_0;
		else
	      videoSt <= VIDEO_OBJECT_LAYER10_2;
	    sysState <= START;
        vd_rd_reg <= 1'b1;
	   end
	else
	   begin
	    sysState <= WAIT;
		if (sysState == WAIT)
	      byte_offset <= byte_offset - 2;
		else
	      byte_offset <= byte_offset +8 -2;
	    videoSt <= VIDEO_OBJECT_LAYER10_2;
        vd_rd_reg <= 1'b0;
	   end
  endrule

  rule wait_1_cycle19 ((videoSt == VIDEO_OBJECT_LAYER10_2_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER10_2; 
	$display("wait_1_cycle19 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code10_2 (videoSt == VIDEO_OBJECT_LAYER10_2);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	sprite_enable <= zeroExtend(tmp[0]);
	byte_boundary <= byte_boundary + 1;
	if (video_object_layer_verid != 4'b0001)
	   begin
		 if (byte_offset < 2)
		   begin
			 byte_offset <= byte_offset + 8 - 1; 
			 if (sysState == WAIT)
			   videoSt <= VIDEO_OBJECT_LAYER10_3_0;
		     else
			   videoSt <= VIDEO_OBJECT_LAYER10_3;
		     sysState <= START;
			 vd_rd_reg <= 1'b1;
		   end
	     else
		   begin
			 sysState <= WAIT;
			 if (sysState == WAIT)
			   byte_offset <= byte_offset - 1;
		     else
			   byte_offset <= byte_offset +8 -1;
		     videoSt <= VIDEO_OBJECT_LAYER10_3;
			 vd_rd_reg <= 1'b0;
		   end
	   end
	else
	  begin
		videoSt <= VIDEO_OBJECT_LAYER11;
		if (sysState == START)
	      begin
			vd_rd_reg <= 1'b0;
			sysState <= WAIT;
			byte_offset <= byte_offset +8 - 1;
		  end
		else
		  byte_offset <= byte_offset - 1;
	  end
  endrule

  rule wait_1_cycle20 ((videoSt == VIDEO_OBJECT_LAYER10_3_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER10_3; 
	$display("wait_1_cycle20 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code10_3 (videoSt == VIDEO_OBJECT_LAYER10_3);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	sprite_enable <= {sprite_enable[0],tmp[0]};
	byte_boundary <= byte_boundary + 1;
	if (sysState == START)
	  begin
		vd_rd_reg <= 1'b0;
		sysState <= WAIT;
		byte_offset <= byte_offset +8 - 1;
      end
    else
	  byte_offset <= byte_offset - 1;
	videoSt <= VIDEO_OBJECT_LAYER11;
  endrule

  rule detect_video_object_layer_start_code11 (videoSt == VIDEO_OBJECT_LAYER11);
    if ((sprite_enable == sTATIC) || (sprite_enable == gMC))
	  begin
	    if (sprite_enable != gMC)
		  begin
			if (byte_offset < 8)
			  begin
	            videoSt <= VIDEO_OBJECT_LAYER11_1_0;
		        vd_rd_reg <= 1'b1;
		        sysState <= START;
		        byte_offset <= byte_offset +8 ;
			  end
			else
	          videoSt <= VIDEO_OBJECT_LAYER11_1;
		  end
		else
		  begin
			if (byte_offset < 6)
			  begin
	            videoSt <= VIDEO_OBJECT_LAYER12_1_0;
		        vd_rd_reg <= 1'b1;
		        sysState <= START;
		        byte_offset <= byte_offset +8 ;
			  end
			else
	          videoSt <= VIDEO_OBJECT_LAYER12;
		  end
	  end
	else
	  videoSt <= VIDEO_OBJECT_LAYER13;
  endrule

  rule wait_1_cycle21 ((videoSt == VIDEO_OBJECT_LAYER11_1_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER11_1; 
	$display("wait_1_cycle21 start code reg %h ",start_code_reg); 
  endrule

  rule wait_1_cycle22 ((videoSt == VIDEO_OBJECT_LAYER12_1_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER12; 
	$display("wait_1_cycle22 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code11_1 (videoSt == VIDEO_OBJECT_LAYER11_1);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	sprite_width <= zeroExtend(tmp[7:0]);
	if (sysState == WAIT)
	  begin
		vd_rd_reg <= 1'b1;
		sysState <= START;
	    videoSt <= VIDEO_OBJECT_LAYER11_2_0;
      end
    else
	  videoSt <= VIDEO_OBJECT_LAYER11_2;
	byte_offset <= byte_offset ;
  endrule

  rule wait_1_cycle23 ((videoSt == VIDEO_OBJECT_LAYER11_2_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER11_2; 
	$display("wait_1_cycle23 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code11_2 (videoSt == VIDEO_OBJECT_LAYER11_2);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	sprite_width <= {sprite_width[7:0],tmp[7:3]};
	marker_bit <= tmp[2];
	sprite_height <= zeroExtend(tmp[1:0]);
	videoSt <= VIDEO_OBJECT_LAYER11_3;
	byte_offset <= byte_offset ;
  endrule

  rule detect_video_object_layer_start_code11_3 (videoSt == VIDEO_OBJECT_LAYER11_3);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	sprite_height <= zeroExtend({sprite_height[1:0],tmp[7:0]});
	videoSt <= VIDEO_OBJECT_LAYER11_4;
	byte_offset <= byte_offset ;
  endrule

  rule detect_video_object_layer_start_code11_4 (videoSt == VIDEO_OBJECT_LAYER11_4);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	sprite_height <= {sprite_height[9:0],tmp[7:5]};
	marker_bit <= tmp[4];
	sprite_left_coordinate <= zeroExtend(tmp[3:0]);
	videoSt <= VIDEO_OBJECT_LAYER11_5;
	byte_offset <= byte_offset ;
  endrule

  rule detect_video_object_layer_start_code11_5 (videoSt == VIDEO_OBJECT_LAYER11_5);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	sprite_left_coordinate <= zeroExtend({sprite_left_coordinate[3:0],tmp[7:0]});
	videoSt <= VIDEO_OBJECT_LAYER11_6;
	byte_offset <= byte_offset ;
  endrule

  rule detect_video_object_layer_start_code11_6 (videoSt == VIDEO_OBJECT_LAYER11_6);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	sprite_left_coordinate <= {sprite_left_coordinate[11:0],tmp[7]};
	marker_bit <= tmp[6];
	sprite_top_coordinate <= zeroExtend(tmp[5:0]);
	videoSt <= VIDEO_OBJECT_LAYER11_7;
	byte_offset <= byte_offset ;
  endrule

  rule detect_video_object_layer_start_code11_7 (videoSt == VIDEO_OBJECT_LAYER11_7);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	sprite_top_coordinate <= {sprite_top_coordinate[5:0],tmp[7:1]}; 
	marker_bit <= tmp[0];
	if ((byte_offset > 14) && (sysState == START))
	  begin
		vd_rd_reg <= 1'b0;
		sysState <= WAIT;
	  end
	videoSt <= VIDEO_OBJECT_LAYER12;
	byte_offset <= byte_offset ;
  endrule

  rule detect_video_object_layer_start_code12 (videoSt == VIDEO_OBJECT_LAYER12);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,6);
	no_of_sprite_warping_points <= tmp[5:0];
	byte_boundary <= byte_boundary + 6;
	if (byte_offset < 9) 
	  begin 
	    if (sysState == WAIT) 
		  videoSt  <= VIDEO_OBJECT_LAYER12_2_0; 
		else 
		  videoSt  <= VIDEO_OBJECT_LAYER12_2; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset    <= byte_offset +8 -6; 
	  end 
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 - 6;
		  end 
		else 
		  byte_offset <= byte_offset - 6; 
        videoSt  <= VIDEO_OBJECT_LAYER12_2; 
      end 
  endrule

  rule wait_1_cycle24 ((videoSt == VIDEO_OBJECT_LAYER12_2_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER12_2; 
	$display("wait_1_cycle24 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code12_2 (videoSt == VIDEO_OBJECT_LAYER12_2);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,3);
	sprite_warping_accuracy <= tmp[2:1];
	sprite_brightness_change <= tmp[0];
	byte_boundary <= byte_boundary + 3;
	if (sprite_enable != gMC)
	  begin
	    if (byte_offset < 4) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER12_3_0; 
		    else 
		      videoSt  <= VIDEO_OBJECT_LAYER12_3; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 -3; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 - 3;
		      end 
		    else 
		      byte_offset <= byte_offset - 3; 
            videoSt  <= VIDEO_OBJECT_LAYER12_3; 
          end 
	  end
	else
	  begin
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 - 3;
		  end 
		else 
		  byte_offset <= byte_offset - 3; 
        videoSt  <= VIDEO_OBJECT_LAYER13; 
	  end
  endrule

  rule wait_1_cycle25 ((videoSt == VIDEO_OBJECT_LAYER12_3_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER12_3; 
	$display("wait_1_cycle25 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code12_3 (videoSt == VIDEO_OBJECT_LAYER12_3);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	low_latency_sprite_enable <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (sysState == START) 
	  begin 
		sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
		byte_offset <= byte_offset +8 - 1;
	  end 
	else 
	  byte_offset <= byte_offset - 1; 
    videoSt  <= VIDEO_OBJECT_LAYER13; 
  endrule

  rule detect_video_object_layer_start_code13 (videoSt == VIDEO_OBJECT_LAYER13);
    if ((video_object_layer_verid != 4'b0001) && (video_object_layer_shape != rECTANGULAR))
	  begin
		if (byte_offset < 1)
		  begin
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8;
            videoSt  <= VIDEO_OBJECT_LAYER13_1_0; 
		  end
		else
          videoSt  <= VIDEO_OBJECT_LAYER13_1; 
	  end
	else
	  begin
		if (byte_offset < 1)
		  begin
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8;
            videoSt  <= VIDEO_OBJECT_LAYER14_1_0; 
		  end
		else
          videoSt  <= VIDEO_OBJECT_LAYER14; 
	  end
  endrule

  rule wait_1_cycle26 ((videoSt == VIDEO_OBJECT_LAYER13_1_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER13_1; 
	$display("wait_1_cycle26 start code reg %h ",start_code_reg); 
  endrule

  rule wait_1_cycle27 ((videoSt == VIDEO_OBJECT_LAYER14_1_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER14; 
	$display("wait_1_cycle27 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code13_1 (videoSt == VIDEO_OBJECT_LAYER13_1);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	sadct_disable <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (byte_offset < 2) 
	  begin 
	    if (sysState == WAIT) 
		  videoSt  <= VIDEO_OBJECT_LAYER14_1_0; 
		else 
		  videoSt  <= VIDEO_OBJECT_LAYER14; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset    <= byte_offset +8 -1; 
	  end 
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 - 1;
		  end 
		else 
		  byte_offset <= byte_offset - 1; 
        videoSt  <= VIDEO_OBJECT_LAYER14; 
      end 
  endrule

  rule detect_video_object_layer_start_code14 (videoSt == VIDEO_OBJECT_LAYER14);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	not_8_bit <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (tmp[0] == 1'b1)
	  begin
    	if (byte_offset < 9) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER15_1_0; 
		    else 
		      videoSt  <= VIDEO_OBJECT_LAYER15; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 -1; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 - 1;
		      end 
		    else 
		      byte_offset <= byte_offset - 1; 
            videoSt  <= VIDEO_OBJECT_LAYER15; 
          end 
	  end
	else
	  begin
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 - 1;
		  end 
		else 
		  byte_offset <= byte_offset - 1; 
        videoSt  <= VIDEO_OBJECT_LAYER16; 
	  end
  endrule

  rule wait_1_cycle28 ((videoSt == VIDEO_OBJECT_LAYER15_1_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER15; 
	$display("wait_1_cycle28 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code15 (videoSt == VIDEO_OBJECT_LAYER15);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	quant_precision <= tmp[7:4];
	bits_per_pixel  <= tmp[3:0];
	if (sysState == START) 
	  begin 
		sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
		byte_offset <= byte_offset +8 - 8;
	  end 
  	else 
	  byte_offset <= byte_offset - 8; 
    videoSt  <= VIDEO_OBJECT_LAYER16; 
  endrule

  rule detect_video_object_layer_start_code16 (videoSt == VIDEO_OBJECT_LAYER16);
	if (video_object_layer_shape == gRAYSCALE)
	   begin
    	if (byte_offset < 3) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER17_1_0; 
		    else 
		      videoSt  <= VIDEO_OBJECT_LAYER17; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8 ;
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 ;
		      end 
		    else 
		      byte_offset <= byte_offset ; 
            videoSt  <= VIDEO_OBJECT_LAYER17; 
          end 
	   end
	else
	   begin
    	if (byte_offset < 1) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER18_1_0; 
		    else 
		      videoSt  <= VIDEO_OBJECT_LAYER18; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8 ;
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 ;
		      end 
		    else 
		      byte_offset <= byte_offset ; 
            videoSt  <= VIDEO_OBJECT_LAYER18; 
          end 
	   end
  endrule

  rule wait_1_cycle29 ((videoSt == VIDEO_OBJECT_LAYER17_1_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER17; 
	$display("wait_1_cycle29 start code reg %h ",start_code_reg); 
  endrule

  rule wait_1_cycle30 ((videoSt == VIDEO_OBJECT_LAYER18_1_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER18; 
	$display("wait_1_cycle30 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code17 (videoSt == VIDEO_OBJECT_LAYER17);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,3);
	no_gray_quant_update <= tmp[2];
	composition_method <= tmp[1];
	linear_composition <= tmp[0];
	byte_boundary <= byte_boundary + 3;
	if (byte_offset < 4) 
	  begin 
	    if (sysState == WAIT) 
		  videoSt  <= VIDEO_OBJECT_LAYER18_1_0; 
		else 
		  videoSt  <= VIDEO_OBJECT_LAYER18; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset    <= byte_offset +8 -3; 
	  end 
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 - 3;
		  end 
		else 
		  byte_offset <= byte_offset - 3; 
        videoSt  <= VIDEO_OBJECT_LAYER18; 
      end 
  endrule

  rule detect_video_object_layer_start_code18 (videoSt == VIDEO_OBJECT_LAYER18);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	quant_type <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (tmp[0] == 1) // QUANT TYPE IS TRUE
	  if (byte_offset < 2) 
	    begin 
	      if (sysState == WAIT) 
		    videoSt  <= VIDEO_OBJECT_LAYER19_1_0; 
		  else 
		    videoSt  <= VIDEO_OBJECT_LAYER19; 
		  sysState <= START; 
		  vd_rd_reg <= 1'b1; 
		  byte_offset    <= byte_offset +8 -1; 
	    end 
	  else
        begin 
	      if (sysState == START) 
		    begin 
			  sysState <= WAIT; 
			  vd_rd_reg <= 1'b0; 
		      byte_offset <= byte_offset +8 - 1;
		    end 
		  else 
		    byte_offset <= byte_offset - 1; 
          videoSt  <= VIDEO_OBJECT_LAYER19; 
        end 
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 - 1;
		  end 
		else 
		  byte_offset <= byte_offset - 1; 
        videoSt  <= VIDEO_OBJECT_LAYER25; 
      end 
  endrule

  rule wait_1_cycle31 ((videoSt == VIDEO_OBJECT_LAYER19_1_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER19; 
	$display("wait_1_cycle31 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code19 (videoSt == VIDEO_OBJECT_LAYER19);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	load_intra_quant_mat <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (tmp[0] == 1) //  LOAD INTRA MATRIX IS TRUE
	  begin
	    if (byte_offset < 9) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER19_2_0; 
		    else 
		      videoSt  <= VIDEO_OBJECT_LAYER19_2; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 -1; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 - 1;
		      end 
		    else 
		      byte_offset <= byte_offset - 1; 
            videoSt  <= VIDEO_OBJECT_LAYER19_2; 
          end 
	  end
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 - 1;
		  end 
		else 
		  byte_offset <= byte_offset - 1; 
        videoSt  <= VIDEO_OBJECT_LAYER25; 
      end 
  endrule

  rule wait_1_cycle32 ((videoSt == VIDEO_OBJECT_LAYER19_2_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER19_2; 
	$display("wait_1_cycle32 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code19_2 (videoSt == VIDEO_OBJECT_LAYER19_2);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	Bit#(6) tmp_counter = counter[5:0] - 1;
	if (counter < 64)
	  begin
		if (tmp[7:0] == 8'd0)
		  begin
	        intra_quant_mat.upd(tmp_counter,intra_quant_mat.sub(tmp_counter-1));
			if (sysState == START)
			  begin
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
				byte_offset <= byte_offset + 8 ;
			  end
		  end
		else
	      intra_quant_mat.upd(tmp_counter,tmp[7:0]);
		counter <= counter + 1;
	  end
	else
	  begin
	    if (byte_offset < 9) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER20_1_0; 
		    else 
		      videoSt  <= VIDEO_OBJECT_LAYER20; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8 ; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 ;
		      end 
		    else 
		      byte_offset <= byte_offset ; 
            videoSt  <= VIDEO_OBJECT_LAYER20; 
          end 
	  end
  endrule

  rule wait_1_cycle33 ((videoSt == VIDEO_OBJECT_LAYER20_1_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER20; 
	$display("wait_1_cycle33 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code20 (videoSt == VIDEO_OBJECT_LAYER20);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	load_nonintra_quant_mat <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (tmp[0] == 1) //  LOAD INTRA MATRIX IS TRUE
	  begin
	    if (byte_offset < 9) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER20_2_0; 
		    else 
		      videoSt  <= VIDEO_OBJECT_LAYER20_2; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 -1; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 - 1;
		      end 
		    else 
		      byte_offset <= byte_offset - 1; 
            videoSt  <= VIDEO_OBJECT_LAYER20_2; 
          end 
	  end
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 - 1;
		  end 
		else 
		  byte_offset <= byte_offset - 1; 
        videoSt  <= VIDEO_OBJECT_LAYER20_2; 
      end 
  endrule

  rule wait_1_cycle34 ((videoSt == VIDEO_OBJECT_LAYER20_2_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER20_2; 
	$display("wait_1_cycle34 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code20_2 (videoSt == VIDEO_OBJECT_LAYER20_2);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	Bit#(6) tmp_counter = counter[5:0] - 1;
	if (counter < 64)
	  begin
		if (tmp[7:0] == 8'd0)
		  begin
	        non_intra_quant_mat.upd(tmp_counter,non_intra_quant_mat.sub(tmp_counter-1));
			if (sysState == START)
			  begin
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
				byte_offset <= byte_offset + 8;
			  end
		  end
		else
	      non_intra_quant_mat.upd(tmp_counter,tmp[7:0]);
		counter <= counter + 1;
	  end
	else
	  begin
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8;
		  end 
		else 
		  byte_offset <= byte_offset ; 
        videoSt  <= VIDEO_OBJECT_LAYER21; 
		counter <= 0;
	  end
  endrule

  rule detect_video_object_layer_start_code21 (videoSt == VIDEO_OBJECT_LAYER21);
    if (video_object_layer_shape == gRAYSCALE)
	  begin
	    if (byte_offset < 1) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER21_1_0; 
		    else 
		      videoSt  <= VIDEO_OBJECT_LAYER21_1; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 ; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 ;
		      end 
		    else 
		      byte_offset <= byte_offset ; 
            videoSt  <= VIDEO_OBJECT_LAYER21_1; 
          end 
	  end
	else
	  begin
        videoSt  <= VIDEO_OBJECT_LAYER24; 
		byte_offset <= byte_offset ; 
	  end
  endrule

  rule wait_1_cycle35 ((videoSt == VIDEO_OBJECT_LAYER21_1_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER21_1; 
	$display("wait_1_cycle35 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code21_1 ((videoSt == VIDEO_OBJECT_LAYER21_1) && 
                                                 (tmp_aux_cnt <= aUX_COMP_COUNT));
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	load_intra_quant_mat_grayscale <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (tmp[0] == 1) //  LOAD INTRA GRAYSCALE MATRIX IS TRUE
	  begin
	    if (byte_offset < 9) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER22_1_0; 
		    else 
		      videoSt  <= VIDEO_OBJECT_LAYER22; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 -1; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 - 1;
		      end 
		    else 
		      byte_offset <= byte_offset - 1; 
            videoSt  <= VIDEO_OBJECT_LAYER22; 
          end 
	  end
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 - 1;
		  end 
		else 
		  byte_offset <= byte_offset - 1; 
        videoSt  <= VIDEO_OBJECT_LAYER23; 
      end 
  endrule

  rule wait_1_cycle36 ((videoSt == VIDEO_OBJECT_LAYER22_1_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER22; 
	$display("wait_1_cycle36 start code reg %h ",start_code_reg); 
  endrule

endrules;
return r;
endfunction
// *************************************************
// End of block1
// *************************************************

// *************************************************
// Start of block2
// *************************************************
function Rules create_block2 ();
 Rules r = rules

  rule detect_video_object_layer_start_code22 (videoSt == VIDEO_OBJECT_LAYER22);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	Bit#(6) tmp_counter = counter[5:0] - 1;
	if (counter < 64)
	  begin
		if (tmp[7:0] == 8'd0)
		  begin
		    if (tmp_aux_cnt == 0)
	           intra_quant_mat_grayscale0.upd(tmp_counter,intra_quant_mat_grayscale0.sub(tmp_counter-1));
		    else if (tmp_aux_cnt == 1)
	           intra_quant_mat_grayscale1.upd(tmp_counter,intra_quant_mat_grayscale1.sub(tmp_counter-1));
		    else if (tmp_aux_cnt == 2)
	           intra_quant_mat_grayscale2.upd(tmp_counter,intra_quant_mat_grayscale2.sub(tmp_counter-1));
			if (sysState == START)
			  begin
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
				byte_offset <= byte_offset + 8;
			  end
		  end
		else
		  begin
		    if (tmp_aux_cnt == 0)
	          intra_quant_mat_grayscale0.upd(tmp_counter,tmp[7:0]);
		    else if (tmp_aux_cnt == 1)
	          intra_quant_mat_grayscale1.upd(tmp_counter,tmp[7:0]);
		    else if (tmp_aux_cnt == 2)
	          intra_quant_mat_grayscale2.upd(tmp_counter,tmp[7:0]);
		  end
		counter <= counter + 1;
	  end
	else
	  begin
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8;
		  end 
		else 
		  byte_offset <= byte_offset ; 
        videoSt  <= VIDEO_OBJECT_LAYER23; 
		counter <= 0;
	  end
  endrule

  rule detect_video_object_layer_start_code23 (videoSt == VIDEO_OBJECT_LAYER23); 
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	load_nonintra_quant_mat_grayscale <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (tmp[0] == 1) //  LOAD INTRA GRAYSCALE MATRIX IS TRUE
	  begin
	    if (byte_offset < 9) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER24_1_0; 
		    else 
		      videoSt  <= VIDEO_OBJECT_LAYER24; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 -1; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 - 1;
		      end 
		    else 
		      byte_offset <= byte_offset - 1; 
            videoSt  <= VIDEO_OBJECT_LAYER24; 
          end 
	  end
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 - 1;
		  end 
		else 
		  byte_offset <= byte_offset - 1; 
        videoSt  <= VIDEO_OBJECT_LAYER24_2; 
      end 
  endrule

  rule detect_video_object_layer_start_code24 (videoSt == VIDEO_OBJECT_LAYER24);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	Bit#(6) tmp_counter = counter[5:0] - 1;
	if (counter < 64)
	  begin
		if (tmp[7:0] == 8'd0)
		  begin
		    if (tmp_aux_cnt == 0)
	          nonintra_quant_mat_grayscale0.upd(tmp_counter,nonintra_quant_mat_grayscale0.sub(tmp_counter-1));
		    else if (tmp_aux_cnt == 1)
	          nonintra_quant_mat_grayscale1.upd(tmp_counter,nonintra_quant_mat_grayscale1.sub(tmp_counter-1));
		    else if (tmp_aux_cnt == 2)
	          nonintra_quant_mat_grayscale2.upd(tmp_counter,nonintra_quant_mat_grayscale2.sub(tmp_counter-1));
			if (sysState == START)
			  begin
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
				byte_offset <= byte_offset + 8;
			  end
		  end
		else
		  begin
		    if (tmp_aux_cnt == 0)
	          nonintra_quant_mat_grayscale0.upd(tmp_counter,tmp[7:0]);
		    else if (tmp_aux_cnt == 1)
	          nonintra_quant_mat_grayscale1.upd(tmp_counter,tmp[7:0]);
		    else if (tmp_aux_cnt == 2)
	          nonintra_quant_mat_grayscale2.upd(tmp_counter,tmp[7:0]);
		  end
		counter <= counter + 1;
	  end
	else
	  begin
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8;
		  end 
		else 
		  byte_offset <= byte_offset ; 
        videoSt  <= VIDEO_OBJECT_LAYER24_2; 
		counter <= 0;
	  end
  endrule

  rule detect_video_object_layer_start_code24_2 (videoSt == VIDEO_OBJECT_LAYER24_2);
    if (tmp_aux_cnt < aUX_COMP_COUNT)
	  begin
        videoSt  <= VIDEO_OBJECT_LAYER21_1; 
		tmp_aux_cnt <= tmp_aux_cnt + 1;
	  end
	else
      videoSt  <= VIDEO_OBJECT_LAYER25; 
  endrule

  rule detect_video_object_layer_start_code25 (videoSt == VIDEO_OBJECT_LAYER25); 
	if (video_object_layer_verid != 4'b0001)
      begin 
	    if (byte_offset < 1) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER25_1_1; 
		    else 
              videoSt  <= VIDEO_OBJECT_LAYER25_1; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 ; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 ;
		      end 
		    else 
		      byte_offset <= byte_offset ; 
            videoSt  <= VIDEO_OBJECT_LAYER25_1; 
          end 
       end 
	else
      begin 
	    if (byte_offset < 1) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER26_1_1; 
		    else 
              videoSt  <= VIDEO_OBJECT_LAYER26; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 ; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 ;
		      end 
		    else 
		      byte_offset <= byte_offset ; 
            videoSt  <= VIDEO_OBJECT_LAYER26; 
          end 
       end 
  endrule

  rule wait_1_cycle37 ((videoSt == VIDEO_OBJECT_LAYER25_1_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER25_1; 
	$display("wait_1_cycle37 start code reg %h ",start_code_reg); 
  endrule

  rule wait_1_cycle38 ((videoSt == VIDEO_OBJECT_LAYER26_1_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER26; 
	$display("wait_1_cycle37 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code25_1 (videoSt == VIDEO_OBJECT_LAYER25_1); 
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	quarter_sample <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (byte_offset < 2) 
	  begin 
	    if (sysState == WAIT) 
		  videoSt  <= VIDEO_OBJECT_LAYER26_1_1; 
		else 
          videoSt  <= VIDEO_OBJECT_LAYER26; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset    <= byte_offset +8 -1 ; 
	  end 
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 -1 ;
		  end 
		else 
		  byte_offset <= byte_offset -1 ; 
        videoSt  <= VIDEO_OBJECT_LAYER26; 
      end 
  endrule

  rule detect_video_object_layer_start_code26 (videoSt == VIDEO_OBJECT_LAYER26); 
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	complexity_estimation_disable <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (tmp[0] == 0)
	  begin
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 -1 ;
		  end 
		else 
		  byte_offset <= byte_offset -1 ; 
        videoSt  <= IDLE;   // define vop complexity header
	  end
	else
	  begin
	    if (byte_offset < 2) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER27_1_1; 
		    else 
              videoSt  <= VIDEO_OBJECT_LAYER27; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 -1 ; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 -1 ;
		      end 
		    else 
		      byte_offset <= byte_offset -1 ; 
            videoSt  <= VIDEO_OBJECT_LAYER27; 
          end 
	  end
  endrule

  rule wait_1_cycle39 ((videoSt == VIDEO_OBJECT_LAYER27_1_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER27; 
	$display("wait_1_cycle37 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code27 (videoSt == VIDEO_OBJECT_LAYER27); 
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	resync_marker_disable <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (byte_offset < 2) 
	  begin 
	    if (sysState == WAIT) 
		  videoSt  <= VIDEO_OBJECT_LAYER28_1_1; 
		else 
          videoSt  <= VIDEO_OBJECT_LAYER28; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset    <= byte_offset +8 -1 ; 
	  end 
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 -1 ;
		  end 
		else 
		  byte_offset <= byte_offset -1 ; 
        videoSt  <= VIDEO_OBJECT_LAYER28; 
      end 
  endrule

  rule wait_1_cycle40 ((videoSt == VIDEO_OBJECT_LAYER28_1_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER28; 
	$display("wait_1_cycle40 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code28 (videoSt == VIDEO_OBJECT_LAYER28); 
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	data_partitioned <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (tmp[0] == 1) // Data is partitioned
	  begin
	    if (byte_offset < 2) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER29_1_1; 
		    else 
              videoSt  <= VIDEO_OBJECT_LAYER29; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 -1 ; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 -1 ;
		      end 
		    else 
		      byte_offset <= byte_offset -1 ; 
            videoSt  <= VIDEO_OBJECT_LAYER29; 
          end 
	  end
	else
	  begin
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 -1 ;
		  end 
		else 
		  byte_offset <= byte_offset -1 ; 
        videoSt  <= VIDEO_OBJECT_LAYER30; 
	  end
  endrule

  rule wait_1_cycle41 ((videoSt == VIDEO_OBJECT_LAYER29_1_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER29; 
	$display("wait_1_cycle41 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code29 (videoSt == VIDEO_OBJECT_LAYER29); 
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	reversible_vlc <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (sysState == START) 
      begin 
		sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
	    byte_offset <= byte_offset +8 -1 ;
	  end 
	else 
	  byte_offset <= byte_offset -1 ; 
    videoSt  <= VIDEO_OBJECT_LAYER30; 
  endrule

  rule detect_video_object_layer_start_code30 (videoSt == VIDEO_OBJECT_LAYER30); 
	if (video_object_layer_verid != 4'b0001)
      begin 
	    if (byte_offset < 1) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER30_1_1; 
		    else 
              videoSt  <= VIDEO_OBJECT_LAYER30_1; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 ; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 ;
		      end 
		    else 
		      byte_offset <= byte_offset ; 
            videoSt  <= VIDEO_OBJECT_LAYER30_1; 
          end 
       end 
	else
      begin 
	    if (byte_offset < 1) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER32_1_1; 
		    else 
              videoSt  <= VIDEO_OBJECT_LAYER32; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 ; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 ;
		      end 
		    else 
		      byte_offset <= byte_offset ; 
            videoSt  <= VIDEO_OBJECT_LAYER32; 
          end 
       end 
  endrule

  rule wait_1_cycle42 ((videoSt == VIDEO_OBJECT_LAYER30_1_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER30_1; 
	$display("wait_1_cycle42 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code30_1 (videoSt == VIDEO_OBJECT_LAYER30_1); 
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	newpred_enable <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (tmp[0] == 1) // NEWPRED_ENABLE IS SET
	  begin
	    if (byte_offset < 3) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER31_1_1; 
		    else 
              videoSt  <= VIDEO_OBJECT_LAYER31_1; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 -1 ; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 -1 ;
		      end 
		    else 
		      byte_offset <= byte_offset -1 ; 
            videoSt  <= VIDEO_OBJECT_LAYER31_1; 
          end 
	  end
	else
	  begin
	    if (byte_offset < 2) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER31_2_1; 
		    else 
              videoSt  <= VIDEO_OBJECT_LAYER31_2; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 -1 ; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 -1 ;
		      end 
		    else 
		      byte_offset <= byte_offset -1 ; 
            videoSt  <= VIDEO_OBJECT_LAYER31_2; 
          end 
	  end
  endrule

  rule wait_1_cycle43 ((videoSt == VIDEO_OBJECT_LAYER31_1_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER31_1; 
	$display("wait_1_cycle43 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code31_1 (videoSt == VIDEO_OBJECT_LAYER31_1); 
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,3);
	requested_upstream_message_type <= tmp[2:1];
	newpred_segment_type <= tmp[0];
	byte_boundary <= byte_boundary + 3;
	if (byte_offset < 4) 
	  begin 
	    if (sysState == WAIT) 
		  videoSt  <= VIDEO_OBJECT_LAYER31_2_1; 
		else 
          videoSt  <= VIDEO_OBJECT_LAYER31_2; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset    <= byte_offset +8 -3 ; 
	  end 
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 -3 ;
		  end 
		else 
		  byte_offset <= byte_offset -3 ; 
        videoSt  <= VIDEO_OBJECT_LAYER31_2; 
      end 
  endrule

  rule wait_1_cycle44 ((videoSt == VIDEO_OBJECT_LAYER31_2_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER31_2; 
	$display("wait_1_cycle44 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code31_2 (videoSt == VIDEO_OBJECT_LAYER31_2); 
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	reduced_resolution_vop_enable <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (byte_offset < 2) 
	  begin 
	    if (sysState == WAIT) 
		  videoSt  <= VIDEO_OBJECT_LAYER32_1_1; 
		else 
          videoSt  <= VIDEO_OBJECT_LAYER32; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset    <= byte_offset +8 -1 ; 
	  end 
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 -1 ;
		  end 
		else 
		  byte_offset <= byte_offset -1 ; 
        videoSt  <= VIDEO_OBJECT_LAYER32; 
      end 
  endrule

  rule detect_video_object_layer_start_code32 (videoSt == VIDEO_OBJECT_LAYER32); 
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	scalability <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (tmp[0] == 1) // scalability is SET
	  begin
	    if (byte_offset < 2) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER32_2_1; 
		    else 
              videoSt  <= VIDEO_OBJECT_LAYER32_2; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 -1 ; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 -1 ;
		      end 
		    else 
		      byte_offset <= byte_offset -1 ; 
            videoSt  <= VIDEO_OBJECT_LAYER32_2; 
          end 
	  end
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 -1 ;
		  end 
		else 
		  byte_offset <= byte_offset -1 ; 
        videoSt  <= VIDEO_OBJECT_LAYER36; 
      end 
  endrule

  rule wait_1_cycle45 ((videoSt == VIDEO_OBJECT_LAYER32_2_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER32_2; 
	$display("wait_1_cycle45 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code32_2 (videoSt == VIDEO_OBJECT_LAYER32_2); 
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	hierarchy_type <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (byte_offset < 9) 
	  begin 
	    if (sysState == WAIT) 
		  videoSt  <= VIDEO_OBJECT_LAYER32_3_1; 
		else 
          videoSt  <= VIDEO_OBJECT_LAYER32_3; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset    <= byte_offset +8 -1 ; 
	  end 
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 -1 ;
		  end 
		else 
		  byte_offset <= byte_offset -1 ; 
        videoSt  <= VIDEO_OBJECT_LAYER32_3; 
      end 
  endrule

  rule wait_1_cycle46 ((videoSt == VIDEO_OBJECT_LAYER32_3_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER32_3; 
	$display("wait_1_cycle46 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code32_3 (videoSt == VIDEO_OBJECT_LAYER32_3);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	ref_layer_id <= tmp[7:4];
	ref_layer_sampling_direc <= tmp[3];
	hor_sampling_factor_n <= zeroExtend(tmp[2:0]);
	byte_offset <= byte_offset ; 
    videoSt  <= VIDEO_OBJECT_LAYER32_4; 
  endrule

  rule detect_video_object_layer_start_code32_4 (videoSt == VIDEO_OBJECT_LAYER32_4);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	hor_sampling_factor_n <= {hor_sampling_factor_n[2:0],tmp[7:6]};
	hor_sampling_factor_m <= tmp[5:1];
	vert_sampling_factor_n <= zeroExtend(tmp[0]);
	byte_offset <= byte_offset ; 
    videoSt  <= VIDEO_OBJECT_LAYER32_5; 
  endrule

  rule detect_video_object_layer_start_code32_5 (videoSt == VIDEO_OBJECT_LAYER32_5);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	vert_sampling_factor_n <= {vert_sampling_factor_n[0],tmp[7:4]};
	vert_sampling_factor_m <= zeroExtend(tmp[3:0]);
	if (byte_offset < 10) 
	  begin 
	    if (sysState == WAIT) 
		  videoSt  <= VIDEO_OBJECT_LAYER32_6_1; 
		else 
          videoSt  <= VIDEO_OBJECT_LAYER32_6; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset    <= byte_offset ; 
	  end 
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset ;
		  end 
		else 
		  byte_offset <= byte_offset - 8 ; 
        videoSt  <= VIDEO_OBJECT_LAYER32_6; 
      end 
  endrule

  rule detect_video_object_layer_start_code32_6 (videoSt == VIDEO_OBJECT_LAYER32_6);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,2);
	vert_sampling_factor_m <= {vert_sampling_factor_m[3:0],tmp[1]};
	enhancement_type <= tmp[0];
	byte_boundary <= byte_boundary + 2;
	if ((video_object_layer_shape == bINARY) && (hierarchy_type == 0))
	// not same in spec
	  begin
	    if (byte_offset < 4) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER33_1_1; 
		    else 
              videoSt  <= VIDEO_OBJECT_LAYER33; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 -2; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 -2;
		      end 
		    else 
		      byte_offset <= byte_offset - 2 ; 
            videoSt  <= VIDEO_OBJECT_LAYER33; 
          end 
	  end
	else
	  begin
	    if (sysState == START) 
	      begin 
		    sysState <= WAIT; 
		    vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 -2 ;
          end 
	    else 
	      byte_offset <= byte_offset -2 ; 
        videoSt  <= VIDEO_OBJECT_LAYER36; 
	  end
  endrule

  rule wait_1_cycle47 ((videoSt == VIDEO_OBJECT_LAYER33_1_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER33; 
	$display("wait_1_cycle47 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code33 (videoSt == VIDEO_OBJECT_LAYER33);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,2);
	use_ref_shape <= tmp[1];
	use_ref_texture <= tmp[0];
	byte_boundary <= byte_boundary + 2;
	if (byte_offset < 10) 
	  begin 
	    if (sysState == WAIT) 
		  videoSt  <= VIDEO_OBJECT_LAYER33_2_1; 
		else 
          videoSt  <= VIDEO_OBJECT_LAYER33_2; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset    <= byte_offset + 8 -2; 
	  end 
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 -2;
		  end 
		else 
		  byte_offset <= byte_offset - 2 ; 
        videoSt  <= VIDEO_OBJECT_LAYER33_2; 
      end 
  endrule

  rule wait_1_cycle48 ((videoSt == VIDEO_OBJECT_LAYER33_2_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER33_2; 
	$display("wait_1_cycle48 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code33_2 (videoSt == VIDEO_OBJECT_LAYER33_2);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	shape_hor_sampling_factor_n <= tmp[7:3];
	shape_hor_sampling_factor_m <= zeroExtend(tmp[2:0]);
	byte_offset <= byte_offset ; 
    videoSt  <= VIDEO_OBJECT_LAYER33_3; 
  endrule

  rule detect_video_object_layer_start_code33_3 (videoSt == VIDEO_OBJECT_LAYER33_3);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	shape_hor_sampling_factor_m <= {shape_hor_sampling_factor_m[2:0],tmp[7:6]};
	shape_vert_sampling_factor_n <= tmp[5:1];
	shape_vert_sampling_factor_m <= zeroExtend(tmp[0]);
	byte_offset <= byte_offset ; 
    videoSt  <= VIDEO_OBJECT_LAYER33_4; 
  endrule

  rule detect_video_object_layer_start_code33_4 (videoSt == VIDEO_OBJECT_LAYER33_4);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	shape_vert_sampling_factor_m <= {shape_vert_sampling_factor_m[0],tmp[7:4]};
	if (sysState == START) 
      begin 
		sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
		byte_offset <= byte_offset +8 -4;
      end 
    else 
	  byte_offset <= byte_offset -4; 
    videoSt  <= VIDEO_OBJECT_LAYER36; 
  endrule

  rule detect_video_object_layer_start_code34 (videoSt == VIDEO_OBJECT_LAYER34); 
	if (video_object_layer_verid != 4'b0001)
      begin 
	    if (byte_offset < 1) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER34_1_1; 
		    else 
              videoSt  <= VIDEO_OBJECT_LAYER34_1; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 ; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 ;
		      end 
		    else 
		      byte_offset <= byte_offset ; 
            videoSt  <= VIDEO_OBJECT_LAYER34_1; 
          end 
       end 
	else
      begin 
	    if (byte_offset < 1) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER35_1; 
		    else 
              videoSt  <= VIDEO_OBJECT_LAYER35; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 ; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 ;
		      end 
		    else 
		      byte_offset <= byte_offset ; 
            videoSt  <= VIDEO_OBJECT_LAYER35; 
          end 
       end 
  endrule

  rule wait_1_cycle49 ((videoSt == VIDEO_OBJECT_LAYER34_1_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER34_1; 
	$display("wait_1_cycle49 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code34_1 (videoSt == VIDEO_OBJECT_LAYER34_1); 
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	scalability <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (tmp[0] == 1) // scalability is SET
	  begin
	    if (byte_offset < 9) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER34_2_1; 
		    else 
              videoSt  <= VIDEO_OBJECT_LAYER34_2; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 -1 ; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 -1 ;
		      end 
		    else 
		      byte_offset <= byte_offset -1 ; 
            videoSt  <= VIDEO_OBJECT_LAYER34_2; 
          end 
	  end
	else
      begin 
	    if (byte_offset < 2) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VIDEO_OBJECT_LAYER35_1; 
		    else 
              videoSt  <= VIDEO_OBJECT_LAYER35; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 -1 ; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 -1 ;
		      end 
		    else 
		      byte_offset <= byte_offset -1 ; 
            videoSt  <= VIDEO_OBJECT_LAYER35; 
          end 
      end 
  endrule

  rule wait_1_cycle50 ((videoSt == VIDEO_OBJECT_LAYER34_2_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER34_2; 
	$display("wait_1_cycle50 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code34_2 (videoSt == VIDEO_OBJECT_LAYER34_2);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	ref_layer_id <= tmp[7:4];
	shape_hor_sampling_factor_n <= zeroExtend(tmp[3:0]);
	byte_offset <= byte_offset ; 
    videoSt  <= VIDEO_OBJECT_LAYER34_3; 
  endrule

  rule detect_video_object_layer_start_code34_3 (videoSt == VIDEO_OBJECT_LAYER34_3);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	shape_hor_sampling_factor_n <= {shape_hor_sampling_factor_n[3:0],tmp[7]};
	shape_hor_sampling_factor_m <= tmp[6:2];
	shape_vert_sampling_factor_n <= zeroExtend(tmp[1:0]);
	byte_offset <= byte_offset ; 
    videoSt  <= VIDEO_OBJECT_LAYER34_4; 
  endrule

  rule detect_video_object_layer_start_code34_4 (videoSt == VIDEO_OBJECT_LAYER34_4);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	shape_vert_sampling_factor_n <= {shape_vert_sampling_factor_n[1:0],tmp[7:5]};
	shape_vert_sampling_factor_m <= tmp[4:0];
	if (byte_offset < 9) 
	  begin 
	    if (sysState == WAIT) 
		  videoSt  <= VIDEO_OBJECT_LAYER35_1; 
		else 
          videoSt  <= VIDEO_OBJECT_LAYER35; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset    <= byte_offset +8 -8 ; 
	  end 
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 -8 ;
		  end 
		else 
		  byte_offset <= byte_offset -8 ; 
        videoSt  <= VIDEO_OBJECT_LAYER35; 
      end 
  endrule

  rule wait_1_cycle51 ((videoSt == VIDEO_OBJECT_LAYER35_1) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER35; 
	$display("wait_1_cycle51 start code reg %h ",start_code_reg); 
  endrule

  rule detect_video_object_layer_start_code35 (videoSt == VIDEO_OBJECT_LAYER35);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	resync_marker_disable <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (sysState == START) 
      begin 
		sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
	    byte_offset <= byte_offset +8 -1 ;
	  end 
	else 
	  byte_offset <= byte_offset -1 ; 
    videoSt  <= VIDEO_OBJECT_LAYER36; 
  endrule

  rule detect_video_object_layer_start_code36 (videoSt == VIDEO_OBJECT_LAYER36);
  //Bit#(5) tmp_byte_boundary = zeroExtend(byte_boundary) + 1;
  Bit#(5) tmp_byte_boundary = 8 - zeroExtend(byte_boundary) ;
    if (byte_offset <= tmp_byte_boundary)
	  begin
	    sysState <= START;
		vd_rd_reg <= 1'b1; 
	    byte_offset <= byte_offset +8 - tmp_byte_boundary;
        videoSt  <= VIDEO_OBJECT_LAYER37_1_0; 
	  end
	else
	  begin
        videoSt  <= VIDEO_OBJECT_LAYER37_1; 
	    byte_offset <= byte_offset - tmp_byte_boundary;
	  end
  endrule

  rule wait_1_cycle52 ((videoSt == VIDEO_OBJECT_LAYER37_1_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VIDEO_OBJECT_LAYER37_1; 
	$display("wait_1_cycle52 start code reg %h ",start_code_reg); 
  endrule

endrules;
return r;
endfunction
// *************************************************
// End of block2
// *************************************************

// *************************************************
// Start of block3
// *************************************************
function Rules create_block3 ();
 Rules r = rules

  rule detect_video_object_layer_next_start_code0 (videoSt == VIDEO_OBJECT_LAYER37_1);
	 sysState <= START;
	 vd_rd_reg <= 1'b1; 
	 if (code_cnt == 2)
	   begin
         videoSt <= VOL_NEXT_START_CODE_DET ; 
		 code_cnt <= 0;
	   end
	 else
	   code_cnt <= code_cnt + 1;
  endrule

  rule detect_video_object_start_code1 (videoSt == VOL_NEXT_START_CODE_DET);
    Tuple3#(Bool,Bit#(4),Bit#(8)) start_code = detstartcode(start_code_reg);
	if (tpl_1(start_code))
	  begin
	    if (tpl_3(start_code) == 8'hB2) // user data start code
		  begin
		    $display("user data start code detected byte_offset %d ",byte_offset);
            videoSt  <= USER_DATA;
			byte_boundary <= 0;
		  end
		else if (tpl_3(start_code) == 8'hB3) // group of vop start code
		  begin
		    $display("group of vop start code detected byte_offset %d ",byte_offset);
            videoSt  <= GROUP_OF_VOP;
		    sysState    <= WAIT;
            vd_rd_reg   <= 1'b0;
	        byte_offset <= zeroExtend(tpl_2(start_code)) + 8;
			byte_boundary <= 0;
			//vop_start_code_detected <= True;
		  end
		else if (tpl_3(start_code) == 8'hB6) // vop start code
		  begin
		    $display("vop start code detected byte_offset %d ",byte_offset);
            videoSt  <= VOP_STATE;
		    sysState    <= WAIT;
            vd_rd_reg   <= 1'b0;
	        byte_offset <= zeroExtend(tpl_2(start_code)) + 8;
			byte_boundary <= 0;
			//vop_start_code_detected <= True;
		  end
		else
		    $display("Error Error Error");
	    //byte_offset <= zeroExtend(tpl_2(start_code)) + 8;
		//sysState    <= WAIT;
        //vd_rd_reg   <= 1'b0;
		$display("start code detected byte_offset %d start_code_reg = %h",byte_offset,start_code_reg);
		if ((sprite_enable == sTATIC) && (low_latency_sprite_enable == 1'b1))
		  $display("Error Error : Simple PROFILE Violated");
	  end
	else
        vd_rd_reg <= 1'b1;
  endrule

  rule user_data0 (videoSt == USER_DATA);
    Tuple3#(Bool,Bit#(4),Bit#(8)) start_code = detstartcode(start_code_reg);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	if (tpl_1(start_code))
	  begin
		if (tpl_3(start_code) == 8'hB3) // group of vop start code
		  begin
		    $display("group of vop start code detected byte_offset %d ",byte_offset);
            videoSt  <= GROUP_OF_VOP;
			byte_boundary <= 0; // since new start code has been detected
			//vop_start_code_detected <= True;
		  end
		else if (tpl_3(start_code) == 8'hB6) // vop start code
		  begin
		    $display("vop start code detected byte_offset %d ",byte_offset);
            videoSt  <= VOP_STATE;
			byte_boundary <= 0; // since new start code has been detected
			//vop_start_code_detected <= True;
		  end
		else
		    $display("Error Error Error");
	    byte_offset <= zeroExtend(tpl_2(start_code)) + 8;
		sysState    <= WAIT;
        vd_rd_reg   <= 1'b0;
		$display("start code detected byte_align_pos %d ",byte_align_pos);
	  end
	else
	  begin
	    user_data_buf.upd(user_data_counter,tpl_3(start_code));
        vd_rd_reg <= 1'b1;
		user_data_counter <= user_data_counter + 1;
	  end
  endrule

  rule group_of_vop0 (videoSt == GROUP_OF_VOP);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	time_code <= zeroExtend(tmp[7:0]);
	if (sysState == WAIT)
	  begin
        videoSt  <= GROUP_OF_VOP_1_0;
		sysState    <= START;
        vd_rd_reg   <= 1'b1;
	  end
	else
      videoSt  <= GROUP_OF_VOP_1;
  endrule

  rule wait_1_cycle53 ((videoSt == GROUP_OF_VOP_1_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= GROUP_OF_VOP_1; 
	$display("wait_1_cycle53 start code reg %h ",start_code_reg); 
  endrule

  rule group_of_vop1 (videoSt == GROUP_OF_VOP_1);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	time_code <= zeroExtend({time_code[7:0],tmp[7:0]});
	if (byte_offset < 10) 
	  begin 
	    if (sysState == WAIT) 
		  videoSt  <= GROUP_OF_VOP_2_0; 
		else 
          videoSt  <= GROUP_OF_VOP_2; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset    <= byte_offset ; 
	  end 
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset ;
		  end 
		else 
		  byte_offset <= byte_offset - 8 ; 
        videoSt  <= GROUP_OF_VOP_2; 
      end 
  endrule

  rule wait_1_cycle54 ((videoSt == GROUP_OF_VOP_2_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= GROUP_OF_VOP_2; 
	$display("wait_1_cycle54 start code reg %h ",start_code_reg); 
  endrule

  rule group_of_vop2 (videoSt == GROUP_OF_VOP_2);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,2);
	time_code <= {time_code[15:0],tmp[1:0]};
	byte_boundary <= byte_boundary + 2;
	if (byte_offset < 4) 
	  begin 
	    if (sysState == WAIT) 
		  videoSt  <= GROUP_OF_VOP_3_0; 
		else 
          videoSt  <= GROUP_OF_VOP_3; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset    <= byte_offset +8 -2; 
	  end 
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset ;
		  end 
		else 
		  byte_offset <= byte_offset - 2 ; 
        videoSt  <= GROUP_OF_VOP_3; 
      end 
  endrule

  rule wait_1_cycle55 ((videoSt == GROUP_OF_VOP_3_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= GROUP_OF_VOP_3; 
	$display("wait_1_cycle55 start code reg %h ",start_code_reg); 
  endrule

  rule group_of_vop3 (videoSt == GROUP_OF_VOP_3);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,2);
	closed_gov <= tmp[1];
	broken_link <= tmp[0];
	byte_boundary <= byte_boundary + 2;
    videoSt  <= GROUP_OF_VOP_4; 
	sysState <= WAIT; 
	vd_rd_reg <= 1'b0; 
	byte_offset <= byte_offset +8 - 2 ; 
  endrule

  rule group_of_vop4 (videoSt == GROUP_OF_VOP_4);
  Bit#(5) tmp_byte_boundary = 8 - zeroExtend(byte_boundary) ;
    if (byte_offset <= tmp_byte_boundary)
	  begin
	    sysState <= START;
		vd_rd_reg <= 1'b1; 
	    byte_offset <= byte_offset +8 - tmp_byte_boundary;
        videoSt  <= GROUP_OF_VOP_5_1_0; 
	  end
	else
	  begin
        videoSt  <= GROUP_OF_VOP_5_1; 
	    byte_offset <= byte_offset - tmp_byte_boundary;
	  end
  endrule

/*
  rule group_of_vop4 (videoSt == GROUP_OF_VOP_4);
  //Bit#(5) tmp_byte_boundary = zeroExtend(byte_boundary) + 1;
  Bit#(5) tmp_byte_boundary = 8 - zeroExtend(byte_boundary);
    if (byte_offset < tmp_byte_boundary)
	  begin
	    sysState <= START;
		vd_rd_reg <= 1'b1; 
	    byte_offset <= byte_offset +8 ;
        videoSt  <= GROUP_OF_VOP_5_0; 
	  end
	else
      videoSt  <= GROUP_OF_VOP_5; 
  endrule
  */

  rule wait_1_cycle_vop5_1 ((videoSt == GROUP_OF_VOP_5_1_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= GROUP_OF_VOP_5_1; 
	$display("wait_1_cycle_vop5_1 start code reg %h ",start_code_reg); 
  endrule

  rule group_of_vop5_1 (videoSt == GROUP_OF_VOP_5_1);
	 sysState <= START;
	 vd_rd_reg <= 1'b1; 
	 if (code_cnt == 5)
	   begin
         videoSt <= VOP_START_CODE_DET ; 
		 code_cnt <= 0;
	   end
	 else
	   code_cnt <= code_cnt + 1;
  endrule

  rule wait_1_cycle56 ((videoSt == GROUP_OF_VOP_5_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= GROUP_OF_VOP_5; 
	$display("wait_1_cycle56 start code reg %h ",start_code_reg); 
  endrule

/*
  rule detect_video_object_layer_next_start_code2 (videoSt == GROUP_OF_VOP_5);
    //Bit#(4) tmp_byte_boundary = zeroExtend(byte_boundary) + 1;
    Bit#(4) tmp_byte_boundary = 8 - zeroExtend(byte_boundary);
    start_code_reg <= byteAlign.flushdata(tmp_byte_boundary,start_code_reg);
    videoSt  <= VOP_START_CODE_DET; 
	sysState <= START;
	byte_boundary <= 0;  // bitstream is byte-aligned now
  endrule
  */

endrules;
return r;
endfunction
// *************************************************
// End of block3
// *************************************************

// *************************************************
// Start of block4
// *************************************************
function Rules create_block4 ();
 Rules r = rules

  rule detect_video_object_start_code3 (videoSt == VOP_START_CODE_DET);
    Tuple3#(Bool,Bit#(4),Bit#(8)) start_code = detstartcode(start_code_reg);
	if (tpl_1(start_code))
	  begin
	    if (tpl_3(start_code) == 8'hB2) // user data start code
		  begin
		    $display("user data start code detected byte_offset %d ",byte_offset);
            videoSt  <= USER_DATA1;
		  end
		else if (tpl_3(start_code) == 8'hB6) // vop start code
		  begin
		    $display("vop start code detected byte_offset %d ",byte_offset);
            videoSt  <= VOP_STATE;
		    sysState    <= WAIT;
            vd_rd_reg   <= 1'b0;
	        byte_offset <= zeroExtend(tpl_2(start_code)) + 8;
			//vop_start_code_detected <= True;
		  end
		else
			// May be need to reset the state-machine at this point
		    $display("Error Error Error");
	    //byte_offset <= zeroExtend(tpl_2(start_code)) + 8;
		//sysState    <= WAIT;
        //vd_rd_reg   <= 1'b0;
		$display("start code detected byte_align_pos %d ",byte_align_pos);
	  end
	else
        vd_rd_reg <= 1'b1;
  endrule

  rule user_data1 (videoSt == USER_DATA1);
    Tuple3#(Bool,Bit#(4),Bit#(8)) start_code = detstartcode(start_code_reg);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	if (tpl_1(start_code))
	  begin
		if (tpl_3(start_code) == 8'hB6) // vop start code
		  begin
		    $display("vop start code detected byte_offset %d ",byte_offset);
            videoSt  <= VOP_STATE;
			byte_boundary <= 0; // since new start code has been detected
			//vop_start_code_detected <= True;
		  end
		else
		    $display("Error Error Error");
	    byte_offset <= zeroExtend(tpl_2(start_code)) + 8;
		sysState    <= WAIT;
        vd_rd_reg   <= 1'b0;
		$display("start code detected byte_align_pos %d ",byte_align_pos);
	  end
	else
	  begin
	    user_data_buf.upd(user_data_counter,tpl_3(start_code));
        vd_rd_reg <= 1'b1;
		user_data_counter <= user_data_counter + 1;
	  end
  endrule

// vop layer starts from here .. the macroblock cnt for AC/DC prediction
// needs to be reset here.
  rule vop_state (videoSt == VOP_STATE);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,2);
	vop_coding_type <= tmp[1:0];
	vop_mb_num_x <= 0;
	vop_mb_num_y <= 0;
	vop_blk_num <= 0;
	mb_num_x <= 0;
	mb_num_y <= 0;
	if (start_code_detected)
	  begin
	    pattern_code_d <= False;
	    pattern_code_2d <= False;
	  end
	else
	  begin
	    if (isIntra)
		  begin
	        pattern_code_d <= True;
	        pattern_code_2d <= True;
		  end
		else
		  begin
	        pattern_code_d <= pattern_code;
	        pattern_code_2d <= pattern_code_d;
		  end
	  end
	blk_cnt <= 0;
	byte_boundary <= byte_boundary + 2;
	if (byte_offset < 3) 
	  begin 
	    if (sysState == WAIT) 
		  videoSt  <= VOP_STATE_1_0; 
		else 
          videoSt  <= VOP_STATE_1; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset    <= byte_offset +8 -2; 
	  end 
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 -2;
		  end 
		else 
		  byte_offset <= byte_offset - 2 ; 
        videoSt  <= VOP_STATE_1; 
      end 
  endrule

  rule wait_1_cycle57 ((videoSt == VOP_STATE_1_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VOP_STATE_1; 
	$display("wait_1_cycle57 start code reg %h ",start_code_reg); 
  endrule

  rule vop_state1 (videoSt == VOP_STATE_1);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	modulo_time_base <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (tmp[0] == 1)
	  begin
	    if (byte_offset < 2) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VOP_STATE_1_0; 
		    else 
              videoSt  <= VOP_STATE_1; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 -1; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 -1;
		      end 
		    else 
		      byte_offset <= byte_offset - 1 ; 
            videoSt  <= VOP_STATE_1; 
          end 
	  end
	else
	  begin
	    if (byte_offset < 2) 
	      begin 
	        if (sysState == WAIT) 
		      videoSt  <= VOP_STATE_2_0; 
		    else 
              videoSt  <= VOP_STATE_2; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 -1; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 -1;
		      end 
		    else 
		      byte_offset <= byte_offset - 1 ; 
            videoSt  <= VOP_STATE_2; 
          end 
	  end
  endrule

  rule wait_1_cycle58 ((videoSt == VOP_STATE_2_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VOP_STATE_2; 
	$display("wait_1_cycle58 start code reg %h ",start_code_reg); 
  endrule

  rule vop_state2 (videoSt == VOP_STATE_2);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	tmp_vop_time_increment_resolution <= vop_time_increment_resolution;
	fvti_num <= 0;
	marker_bit <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (sysState == START) 
	  begin 
	    sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
		byte_offset <= byte_offset +8 -1;
	  end 
    else 
	  byte_offset <= byte_offset - 1 ; 
    videoSt  <= VOP_STATE_CAL_FVTI; 
  endrule

  rule  vop_state_cal_fvti (videoSt == VOP_STATE_CAL_FVTI);
    vop_time_increment <= 0;
    if (tmp_vop_time_increment_resolution == 0)
	  begin
		if (byte_offset < fvti_num)
		  begin
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8 ; 
            videoSt  <= VOP_STATE_2_1_0; 
		  end
		else
          videoSt  <= VOP_STATE_2_1; 
	  end
	else
	  begin
       tmp_vop_time_increment_resolution  <= tmp_vop_time_increment_resolution >> 1;
	   fvti_num <= fvti_num + 1;
	  end
  endrule

  rule wait_1_cycle58_0 ((videoSt == VOP_STATE_2_1_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VOP_STATE_2_1; 
	$display("wait_1_cycle58_0 start code reg %h ",start_code_reg); 
  endrule

  rule vop_state2_1 (videoSt == VOP_STATE_2_1);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
    if (fvti_num > 8)
	  begin
		fvti_num <= fvti_num - 8;
	    vop_time_increment <= {vop_time_increment[7:0],tmp[7:0]};
	  end
	else
	  begin
        videoSt  <= VOP_STATE_2_2; 
	    if (sysState == START) 
	      begin 
		    sysState <= WAIT; 
		    vd_rd_reg <= 1'b0; 
	        byte_offset <= byte_offset + 8 ;
	      end 
	    else 
	      byte_offset <= byte_offset ;
	  end
  endrule

  rule vop_state2_2 (videoSt == VOP_STATE_2_2);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,fvti_num[3:0]);
	vop_time_increment <= byteAlign.bs(vop_time_increment,tmp,fvti_num[3:0]);
	byte_boundary <= byte_boundary + fvti_num[2:0];
	if (sysState == START) 
	  begin 
		sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
	    byte_offset <= byte_offset +8 - fvti_num;
	  end 
	else 
	  byte_offset <= byte_offset - fvti_num; 
    videoSt  <= VOP_STATE_2_3; 
  endrule

  rule vop_state_2_3 (videoSt == VOP_STATE_2_3) ; 
	if (byte_offset < 1) 
	  begin 
	    if (sysState == WAIT) 
	      videoSt  <= VOP_STATE_2_4_0; 
		else 
          videoSt  <= VOP_STATE_2_4; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset    <= byte_offset +8 ; 
	  end 
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 ;
		  end 
		else 
		  byte_offset <= byte_offset ; 
        videoSt  <= VOP_STATE_2_4; 
      end 
  endrule

  rule wait_1_cycle58_1 ((videoSt == VOP_STATE_2_4_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VOP_STATE_2_4; 
	$display("wait_1_cycle58_1 start code reg %h ",start_code_reg); 
  endrule

  rule vop_state2_4 (videoSt == VOP_STATE_2_4);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	marker_bit <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (byte_offset < 9) 
	  begin 
	    if (sysState == WAIT) 
	      videoSt  <= VOP_STATE_3_0; 
		else 
          videoSt  <= VOP_STATE_3; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset    <= byte_offset +8 -1; 
	  end 
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 -1;
		  end 
		else 
		  byte_offset <= byte_offset - 1 ; 
        videoSt  <= VOP_STATE_3; 
      end 
  endrule

  rule wait_1_cycle58_1_0 ((videoSt == VOP_STATE_3_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VOP_STATE_3; 
	$display("wait_1_cycle58_1_0 start code reg %h ",start_code_reg); 
  endrule

  rule vop_state3 (videoSt == VOP_STATE_3);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	vop_coded <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (tmp[0] == 0)
	  begin
	    videoSt  <= GROUP_OF_VOP_4; 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 -1;
		  end 
		else 
		  byte_offset <= byte_offset - 1 ; 
	  end
	else
	  begin
	    videoSt  <= VOP_STATE_3_0_0; 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 -1;
		  end 
		else 
		  byte_offset <= byte_offset - 1 ; 
	  end
  endrule

  rule vop_state3_0 (videoSt == VOP_STATE_3_0_0);
	if ((video_object_layer_shape != bINARY) && (vop_coding_type == 1))
	  begin
	    if (byte_offset < 2) 
	      begin 
	        if (sysState == WAIT) 
	          videoSt  <= VOP_STATE_3_1_0; 
		    else 
              videoSt  <= VOP_STATE_3_1; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 ; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 ;
		      end 
		    else 
		      byte_offset <= byte_offset  ; 
            videoSt  <= VOP_STATE_3_1; 
	      end
	  end
	else
	  begin
	    videoSt  <= VOP_STATE_4_0_0; 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 ;
		  end 
		else 
		  byte_offset <= byte_offset ; 
	  end
  endrule

  rule wait_1_cycle59_0 ((videoSt == VOP_STATE_3_1_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VOP_STATE_3_1; 
	$display("wait_1_cycle59_0 start code reg %h ",start_code_reg); 
  endrule

  rule vop_state3_1 (videoSt == VOP_STATE_3_1);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	vop_rounding_type <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	videoSt  <= VOP_STATE_4_0_0; 
	if (sysState == START) 
	   begin 
		 sysState <= WAIT; 
		 vd_rd_reg <= 1'b0; 
		 byte_offset <= byte_offset +8 -1;
	   end 
    else 
	  byte_offset <= byte_offset - 1 ; 
  endrule

  rule vop_state4_0_0 (videoSt == VOP_STATE_4_0_0);
	if ((reduced_resolution_vop_enable == 1) && (video_object_layer_shape == rECTANGULAR) && 
	         ((vop_coding_type == 0) || (vop_coding_type == 1)))
	  begin
	    if (byte_offset < 2) 
	      begin 
	        if (sysState == WAIT) 
	          videoSt  <= VOP_STATE_4_0; 
		    else 
              videoSt  <= VOP_STATE_4; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 ; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 ;
		      end 
		    else 
		      byte_offset <= byte_offset ; 
            videoSt  <= VOP_STATE_4; 
          end 
	  end
	else 
	  begin
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 ;
		  end 
		else 
		  byte_offset <= byte_offset ; 
        videoSt  <= VOP_STATE_5; 
	  end
  endrule

  rule wait_1_cycle59 ((videoSt == VOP_STATE_4_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VOP_STATE_4; 
	$display("wait_1_cycle59 start code reg %h ",start_code_reg); 
  endrule

  rule vop_state4 (videoSt == VOP_STATE_4);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	vop_reduced_resolution <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	if (sysState == START) 
	  begin 
		sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
		byte_offset <= byte_offset +8 -1;
	  end 
    else 
	  byte_offset <= byte_offset - 1 ; 
    videoSt  <= VOP_STATE_5; 
  endrule

  rule vop_state5 (videoSt == VOP_STATE_5);
	if ((video_object_layer_shape != bINARY_ONLY) && (complexity_estimation_disable == 0))
      videoSt  <= VOP_STATE_4_READ_VOP_COMPLEXITY_ESTIMATION_HEADER; 
    else
      videoSt  <= VOP_STATE_5_1; 
  endrule

  rule vop_state5_1 (videoSt == VOP_STATE_5_1);
	if (video_object_layer_shape != bINARY_ONLY)
	  begin
	    if (byte_offset < 3) 
	      begin 
	        if (sysState == WAIT) 
	          videoSt  <= VOP_STATE_6_0; 
		    else 
              videoSt  <= VOP_STATE_6; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 ; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 ;
		      end 
		    else 
		      byte_offset <= byte_offset ; 
            videoSt  <= VOP_STATE_6; 
          end 
	  end
	else
      videoSt  <= VOP_STATE_7;
  endrule

  rule wait_1_cycle60 ((videoSt == VOP_STATE_6_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VOP_STATE_6; 
	$display("wait_1_cycle60 start code reg %h ",start_code_reg); 
  endrule

  rule vop_state6 (videoSt == VOP_STATE_6);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,3);
	intra_dc_vlc_thr <= tmp[2:0];
	byte_boundary <= byte_boundary + 3;
	if (sysState == START) 
	  begin 
		sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
		byte_offset <= byte_offset +8 -3;
	  end 
    else 
	  byte_offset <= byte_offset - 3 ; 
    videoSt  <= VOP_STATE_7; 
  endrule

  rule vop_state7 (videoSt == VOP_STATE_7);
	if (video_object_layer_shape != bINARY_ONLY)
	  begin
	    if (byte_offset < zeroExtend(quant_precision)) 
	      begin 
	        if (sysState == WAIT) 
	          videoSt  <= VOP_STATE_8_0; 
		    else 
              videoSt  <= VOP_STATE_8; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset    <= byte_offset +8 ; 
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 ;
		      end 
		    else 
		      byte_offset <= byte_offset ; 
            videoSt  <= VOP_STATE_8; 
          end 
	  end
	else
      videoSt  <= VOP_STATE_9;
  endrule

  rule wait_1_cycle61 ((videoSt == VOP_STATE_8_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VOP_STATE_8; 
	$display("wait_1_cycle60 start code reg %h ",start_code_reg); 
  endrule

  rule vop_state8 (videoSt == VOP_STATE_8);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,quant_precision);
	vop_quant <= tmp;
	running_QP <= tmp;
	byte_boundary <= byte_boundary + quant_precision[2:0];
	if (sysState == START) 
	  begin 
		sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
		byte_offset <= byte_offset +8 -zeroExtend(quant_precision);
	  end 
    else 
	  byte_offset <= byte_offset - zeroExtend(quant_precision) ; 
    videoSt  <= VOP_STATE_9; 
  endrule

  rule vop_state9 (videoSt == VOP_STATE_9);
	if (vop_coding_type != 0) // vop_coding _type is NOT I
	  begin
	    if (byte_offset < 3) 
	      begin 
	        if (sysState == WAIT) 
	          videoSt  <= VOP_STATE_10_0; 
		    else 
              videoSt  <= VOP_STATE_10; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8 ;
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8;
		      end 
		    else 
		      byte_offset <= byte_offset ; 
            videoSt  <= VOP_STATE_10; 
          end 
	  end
	else
      videoSt  <= VOP_STATE_11;
  endrule

  rule wait_1_cycle62 ((videoSt == VOP_STATE_10_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= VOP_STATE_10; 
	$display("wait_1_cycle60 start code reg %h ",start_code_reg); 
  endrule

  rule vop_state10 (videoSt == VOP_STATE_10);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,3);
	vop_fcode_forward <= tmp[2:0];
	byte_boundary <= byte_boundary + 3;
	if (scalability == 1)
	  begin
	    $display("Error Error !! Scalablity is Set");
        videoSt  <= SUSPEND; 
	  end
	else
	  begin
	    if (vop_start_code_detected)
          videoSt  <= SUSPEND; 
		else
		  // motion shape texture decoding starts here
          videoSt  <= VOP_STATE_11;  
	  end
	if (sysState == START) 
	  begin 
		sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
		byte_offset <= byte_offset +8 -3;
	  end 
    else 
	  byte_offset <= byte_offset - 3;
  endrule

  rule write_PSState_in_suspend ((host_strobe.wget == Just(1)) &&
                      (host_select.wget == Just(0)) &&
					  (host_address.wget == Just(1))&&
					  (videoSt == SUSPEND));
      if (host_datain.wget == Just(2))
	     begin
	       videoSt <= RESUME;	
		   $display("resume is set");
	     end
  endrule

  rule resume_decoding (videoSt == RESUME);
    videoSt  <= VOP_STATE_11; 
	vop_start_code_detected <= False;
  endrule

  rule vop_state11 (videoSt == VOP_STATE_11);
    if (data_partitioned == 1)
      videoSt  <= DATA_PARTITIONED_MST; // data partitioned motion shape texture
	else   
      videoSt  <= COMBINED_MST ; // combined motion shape texture
  endrule

  rule combined_mst0((videoSt == COMBINED_MST0) && (blkBuffer.busy == False));
    if (isIntra || (!isIntra && (cbpc[0] == 1)))
	  begin
	    $display("//////// Flushing last block in MB");
		blkBuffer.sent_output_data(1'b1);
	    videoSt <= COMBINED_MST_0_1;
		pattern_code_d <= False;
		pattern_code_2d <= False;
	  end
	else
	  videoSt <= COMBINED_MST_0_2;
  endrule

  rule combined_mst_0_1(videoSt == COMBINED_MST_0_1);
    $display("clear signal");
	blkBuffer.clear_d(1'b1); // send clear signal
	videoSt <= COMBINED_MST_0_2;
  endrule

  rule combined_mst_0_2(videoSt == COMBINED_MST_0_2);
    if (mb_done.wget == Just(1))
	  begin
	    videoSt <= COMBINED_MST;
		disable_mb_done_reg <= 1'b1;
	  end
  endrule

  rule combined_mst ((videoSt == COMBINED_MST) && (blkBuffer.busy == False));
    disable_mb_done_reg <= 1'b0;
    if (vop_coding_type != 0) // VOP is NOT "I"
	  begin
	    if (byte_offset < 1) 
	      begin 
	        if (sysState == WAIT) 
	          videoSt  <= MB_STATE_1_0; 
		    else 
              videoSt  <= MB_STATE_1; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8 ;
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8;
		      end 
		    else 
		      byte_offset <= byte_offset ; 
            videoSt  <= MB_STATE_1; 
          end 
	  end
	else
	  begin
        videoSt  <= MB_STATE_2; 
		not_coded <= 0;
	  end
	first_MB <= True;
  endrule

endrules;
return r;
endfunction
// *************************************************
// End of block4
// *************************************************

// *************************************************
// Start of block5
// *************************************************
function Rules create_block5 ();
 Rules r = rules

  rule wait_mb_state_1_0 ((videoSt == MB_STATE_1_0) && (vd_valid.wget == Just(1))) ;
	 videoSt <= MB_STATE_1;
	 $display("wait_1_mb_state_1_0 start code reg %h ",start_code_reg);
  endrule

  rule mb_state_1 (videoSt == MB_STATE_1);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	not_coded <= tmp[0];
	/*
	if (video_packet_header_detected && (vop_coding_type == 1))
	  begin
	    isIntra_d <= False;
	    $display("isIntra_d is False as P frame and video_packet_header_detected");
	  end
	else
	  begin
	    if (isIntra)
	      $display("isIntra_d is True");
	    else
	      $display("isIntra_d is False");
	    isIntra_d <= isIntra; // since if MB is not coded we will never get updated value of intra_d from MB_STATE_3
	  end
	  */
	if (isIntra)
	  $display("isIntra_d is True");
	else
	  $display("isIntra_d is False");

	// since if MB is not coded we will never 
	//get updated value of intra_d from MB_STATE_3

	isIntra_d <= isIntra; 
	mbtype <= 5 ; // reserved value of mbtype has been used here
	              // becoz after each MB if mbtype is needs to be
				  // defined and if its not required then wont matter
	byte_boundary <= byte_boundary + 1;
	if (sysState == START) 
	  begin 
		sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
		byte_offset <= byte_offset +8 -1;
	  end 
    else 
	  byte_offset <= byte_offset -1; 
    videoSt  <= MB_STATE_2; 
  endrule

  rule mb_state_2 (videoSt == MB_STATE_2);
    if ((not_coded == 0) || (vop_coding_type == 0)) // VOP_CODING is "I"
	  begin
	    if (byte_offset < 9) 
	      begin 
	        if (sysState == WAIT) 
	          videoSt  <= MB_STATE_3_0; 
		    else 
              videoSt  <= MB_STATE_3; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8 ;
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8;
		      end 
		    else 
		      byte_offset <= byte_offset ; 
            videoSt  <= MB_STATE_3; 
          end 
	  end
	else
	  begin
	    //cbpy <= 0;
		//cbpc <= 0;
		//blk_cnt <= 0;
		//pattern_code_d <= pattern_code;
		//pattern_code_2d <= pattern_code_d;
		$display("**********************************");
		$display("Macroblock is not coded and P type");
		$display("**********************************");
		$display("Moving to MB_BLK_STATE");
		// need to wait for 64*6 cycles and move forward
		// blkBuffer and read them out before 
		// going forward
        videoSt  <= UPDATE_MV_BUFFER; 
        mbheaderfifo.enq(tuple7(mbNum,1,0,0,0,0,0));
		$display("writing mvPredBuffer addr = %d data = 0",mv_addr);
        mvPredBuffer_x.upd(mv_addr,Just(0));
        mvPredBuffer_y.upd(mv_addr,Just(0));
		update_cnt <= 1;
	  end
  endrule

  rule update_mv_buffer(videoSt == UPDATE_MV_BUFFER);
	 if (update_cnt !=4)
	   begin
		 $display("writing mvPredBuffer addr = %d data = 0",mv_addr);
         mvPredBuffer_x.upd(mv_addr,Just(0));
         mvPredBuffer_y.upd(mv_addr,Just(0));
		 update_cnt <= update_cnt + 1;
	   end
	 else
	   begin
		 update_cnt <= 0;
         videoSt <= MB_not_coded_wait_state;
	   end
  endrule

/*
  rule mb_not_coded_wait_state  (videoSt == MB_not_coded_wait_state);
    if (blkBuffer.busy == False)
	  begin
		if ((!isIntra_d && (cbpc[0] == 1)) || 
		    (isIntra_d && !((mb_num_x == 0) && (mb_num_y == 0)) && !video_packet_header_detected))
		  begin
		    blkBuffer.sent_output_data(1'b1);
		    //isIntra_d <= False;
		  end
	    wait_cnt <= 1;
        videoSt  <= MB_not_coded_wait_state_1; 
	  end
  endrule
  */

  rule mb_not_coded_wait_state  (videoSt == MB_not_coded_wait_state);
	wait_cnt <= 1;
    videoSt  <= MB_not_coded_wait_state_1; 
  endrule

  rule mb_not_coded_wait_state_1  (videoSt == MB_not_coded_wait_state_1);
    /*
	if ((cbpc[0] == 1) || (isIntra_d && (mb_num_x != 0) && (mb_num_y != 0)))
	  begin
        $display("clear signal");
	    blkBuffer.clear_d(1'b1); // send clear signal
      end
	  */
	wait_cnt <= 2;
    videoSt  <= MB_not_coded_wait_state_2; 
	cbpy <= 0;
	cbpc <= 0;
	blk_cnt <= 0;
	pattern_code_d <= False;
	pattern_code_2d <= False;
	acdcpredbuf_cur_addr <= current_address;
  endrule

  rule mb_not_coded_wait_state_2  (videoSt == MB_not_coded_wait_state_2);
    Bit#(7) wait_cnt_6_0 = wait_cnt[6:0];
    Bit#(6) wait_cnt_5_0 = wait_cnt[5:0];
	if (wait_cnt == 384)
	   begin
		 wait_cnt <= 0;
		 blk_cnt <= 0;
         videoSt  <= CHECK_RESYNC_MARKER0; 
		 if (zeroExtend(vop_mb_num_x) == (mb_width-1))
		   begin
			 vop_mb_num_x <= 0;
			 vop_mb_num_y <= vop_mb_num_y + 1;
		   end
	     else
		   vop_mb_num_x <= vop_mb_num_x + 1;
		 if (zeroExtend(mb_num_x) == (mb_width -1))
		   begin
			 mb_num_x <= 0;
			 mb_num_y <= mb_num_y + 1;
		   end
		 else if ((zeroExtend(mb_num_y) == (mb_height -1)) && (zeroExtend(mb_num_x) == (mb_width -1)))
		   begin
			 mb_num_x <= 0;
			 mb_num_y <= 0;
		   end
		 else
		   mb_num_x <= mb_num_x + 1;
	     //mb_num_y_d <= mb_num_y;
	   end
	else
	  begin
	    wait_cnt <= wait_cnt + 1;
		if (wait_cnt_5_0 == 62)
		  blk_cnt <= blk_cnt + 1;
		else if (wait_cnt_5_0 == 63)
	      acdcpredbuf_cur_addr <= current_address;
		else if ((wait_cnt_5_0 > 15) && (wait_cnt_5_0 < 31))
	      begin
	        acdcPredBuffer.upd(acdcpredbuf_cur_addr,Nothing);
	        //$display("writing acdcPredBuffer addr = %d data = Nothing wait_cnt = %h",acdcpredbuf_cur_addr,wait_cnt);
	        acdcpredbuf_cur_addr <= acdcpredbuf_cur_addr + 1;
		  end
	  end
  endrule

  rule wait_1_cycle63 ((videoSt == MB_STATE_3_0) && (vd_valid.wget == Just(1))) ; 
    if (byte_offset >= 9)
      videoSt <= MB_STATE_3; 
	else
	  byte_offset <= byte_offset + 8;
	$display("wait_1_cycle60 start code reg %h ",start_code_reg); 
  endrule

  rule mb_state_3 (videoSt == MB_STATE_3);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,9);
    Tuple3#(Bit#(3),Bit#(2),Bit#(5)) mcbpc;
	$display("mb_state_3 tmp = %h",tmp);
	if (vop_coding_type == 0) // "I" type
	  mcbpc = decode_mcbpcI(tmp[8:0]);
	else
	  mcbpc = decode_mcbpcP(tmp[8:0]);
	//isIntra_d <= isIntra;
	mbtype <= tpl_1(mcbpc);
	cbpc <=   tpl_2(mcbpc);
	let tmp_byte_boundary = tpl_3(mcbpc);
	byte_boundary <= byte_boundary  + tmp_byte_boundary[2:0];
	if (sysState == START) 
	  begin 
	    sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
	    byte_offset <= byte_offset + 8 - tpl_3(mcbpc);
	  end 
    else 
	  byte_offset <= byte_offset - tpl_3(mcbpc);
    videoSt  <= MB_STATE_4; 
	$display("mcbpc  mbtype = %d cbpc = %d alignment = %d",tpl_1(mcbpc),tpl_2(mcbpc),tpl_3(mcbpc));
  endrule

  rule mb_state_4 (videoSt == MB_STATE_4);
	if ((short_video_header == False) && isIntra)
	  begin
	    if (byte_offset < 1) 
	      begin 
	        if (sysState == WAIT) 
	          videoSt  <= MB_STATE_5_0; 
		    else 
              videoSt  <= MB_STATE_5; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8 ;
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8;
		      end 
		    else 
		      byte_offset <= byte_offset ; 
            videoSt  <= MB_STATE_5; 
          end 
	  end
	else
      videoSt  <= MB_STATE_6; 
  endrule

  rule wait_1_cycle_mb_state_5_0 ((videoSt == MB_STATE_5_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= MB_STATE_5; 
	$display("wait_1_cycle_mb_state_5_0 start code reg %h ",start_code_reg); 
  endrule

  rule mb_state_5 ((videoSt == MB_STATE_5) && (update_cnt < 5));
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	if (update_cnt != 4)
	  begin
		$display("writing mvPredBuffer addr = %d data = 0",mv_addr);
        mvPredBuffer_x.upd(mv_addr,Just(0)); // Intra blocks are treated as 0 and not as invalid
        mvPredBuffer_y.upd(mv_addr,Just(0));
		update_cnt <= update_cnt+ 1;
	  end
	else
	  begin
		update_cnt <= 0;
	    ac_pred_flag <= tmp[0];
	    byte_boundary <= byte_boundary + 1;
        mbheaderfifo.enq(tuple7(mbNum,0,cbpy,cbpc,0,0,0));
	    if (sysState == START) 
	      begin 
	        sysState <= WAIT; 
		    vd_rd_reg <= 1'b0; 
	        byte_offset <= byte_offset + 8 - 1;
	      end 
        else 
	      byte_offset <= byte_offset - 1;
        videoSt  <= MB_STATE_6; 
	  end
  endrule

  rule mb_state_6 (videoSt == MB_STATE_6);
    if (mbtype != 7) // mbtype is NOT STUFFING
	  begin 
	    if (byte_offset < 6) 
	      begin 
	        if (sysState == WAIT) 
	          videoSt  <= MB_STATE_7_0; 
		    else 
              videoSt  <= MB_STATE_7; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8 ;
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8;
		      end 
		    else 
		      byte_offset <= byte_offset ; 
            videoSt  <= MB_STATE_7; 
          end 
	  end 
	else
      videoSt  <= MST_STATE_0; 
  endrule

  rule wait_1_cycle64 ((videoSt == MB_STATE_7_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= MB_STATE_7; 
	$display("wait_1_cycle64 start code reg %h ",start_code_reg); 
  endrule

  rule mb_state_7 (videoSt == MB_STATE_7);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,6);
    Tuple2#(Bit#(4),Bit#(5)) cbpy_code; 
	$display("mb_state_7 tmp = %h",tmp);
	if (isIntra) // "I" type
	  cbpy_code = decode_cbpyI(tmp[5:0]);
	else
	  cbpy_code = decode_cbpyP(tmp[5:0]);
	cbpy <= tpl_1(cbpy_code);
	let tmp_byte_boundary = tpl_2(cbpy_code);
	byte_boundary <= byte_boundary + tmp_byte_boundary[2:0];
	if (sysState == START) 
	  begin 
	    sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
	    byte_offset <= byte_offset + 8 - tpl_2(cbpy_code);
	  end 
    else 
	  byte_offset <= byte_offset - tpl_2(cbpy_code);
    videoSt  <= MB_STATE_8; 
	$display("cbpy  = %b alignment = %d",tpl_1(cbpy_code),tpl_2(cbpy_code));
  endrule

  rule mb_state_8 (videoSt == MB_STATE_8);
	if ((mbtype == 1) || (mbtype == 4)) 
	  begin
	    if (byte_offset < 2) 
	      begin 
	        if (sysState == WAIT) 
	          videoSt  <= MB_STATE_9_0; 
		    else 
              videoSt  <= MB_STATE_9; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8 ;
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 ;
		      end 
		    else 
		      byte_offset <= byte_offset ;
            videoSt  <= MB_STATE_9; 
          end 
	  end
	else
      videoSt  <= MB_STATE_10; 
  endrule

  rule wait_1_cycle65 ((videoSt == MB_STATE_9_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= MB_STATE_9; 
	$display("wait_1_cycle65 start code reg %h ",start_code_reg); 
  endrule

  // dquant code is decoded
  rule mb_state_9 (videoSt == MB_STATE_9);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,2);
	/*
	case (tmp[1:0])
	  2'b00 : running_QP <= vop_quant - 1;
	  2'b01 : running_QP <= vop_quant - 2;
	  2'b10 : running_QP <= vop_quant + 1;
	  2'b11 : running_QP <= vop_quant + 2;
	  default : running_QP <= vop_quant;
	endcase
	*/
	// changed to running_QP as that can updated
	// by vop_quant,dquant,quant_scale
	case (tmp[1:0]) 
	  2'b00 : running_QP <= running_QP - 1;
	  2'b01 : running_QP <= running_QP - 2;
	  2'b10 : running_QP <= running_QP + 1;
	  2'b11 : running_QP <= running_QP + 2;
	  default : running_QP <= running_QP;
	endcase
	// May be check for saturation ??? 
	byte_boundary <= byte_boundary + 2;
	if (sysState == START) 
	  begin 
	    sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
	    byte_offset <= byte_offset + 8 - 2;
	  end 
    else 
	  byte_offset <= byte_offset - 2;
    videoSt  <= MB_STATE_10; 
  endrule

  rule mb_state_10 (videoSt == MB_STATE_10);
	case (intra_dc_vlc_thr)
	  3'b000 : use_intra_dc_vlc <= True;
	  3'b001 : use_intra_dc_vlc <= (running_QP < 13);
	  3'b010 : use_intra_dc_vlc <= (running_QP < 15);
	  3'b011 : use_intra_dc_vlc <= (running_QP < 17);
	  3'b100 : use_intra_dc_vlc <= (running_QP < 19);
	  3'b101 : use_intra_dc_vlc <= (running_QP < 21);
	  3'b110 : use_intra_dc_vlc <= (running_QP < 23);
	  3'b111 : use_intra_dc_vlc <= False;
	  default : use_intra_dc_vlc <= False;
	endcase
    if ((((mbtype == 0) || (mbtype == 1)) && (vop_coding_type == 1) && (mvp_done == False)) || // "P" frame
		(mbtype == 2 && mv_count != 3))
      videoSt  <= MV_STATE_1; 
	else
	  begin
        if (mvp_done && (update_cnt < 4))
		   begin
	         horizontal_mv_data.upd(update_cnt[1:0],horizontal_mv_data.sub(0));
	         horizontal_mv_residual.upd(update_cnt[1:0],horizontal_mv_residual.sub(0));
	         vertical_mv_data.upd(update_cnt[1:0],vertical_mv_data.sub(0));
	         vertical_mv_residual.upd(update_cnt[1:0],vertical_mv_residual.sub(0));
			 update_cnt <= update_cnt + 1;
		   end
		else
		   begin
		     if (isInter == 1)
                videoSt  <= EXEC_MV_PREDICTION; 
		     else
               videoSt  <= MB_BLK_STATE; 
			 mvp_done <= False;
			 update_cnt <= 0;
			 //update_cnt <= 1;
		   end
	  end
  endrule

endrules;
return r;
endfunction
// *************************************************
// End of block5
// *************************************************

// *************************************************
// Start of block6
// *************************************************
function Rules create_block6 ();
 Rules r = rules

  rule mv_state_1 (videoSt == MV_STATE_1);
	if (byte_offset < 5) 
	  begin 
	    if (sysState == WAIT) 
	      videoSt  <= MV_STATE_2_0;
		else 
          videoSt  <= MV_STATE_2; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset <= byte_offset +8 ;
	  end 
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 ;
		  end 
		else 
		  byte_offset <= byte_offset ;
        videoSt  <= MV_STATE_2; 
      end 
  endrule

  rule wait_1_cycle66 ((videoSt == MV_STATE_2_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= MV_STATE_2; 
	$display("wait_1_cycle66 start code reg %h ",start_code_reg); 
  endrule

  rule mv_state_2 (videoSt == MV_STATE_2);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,5);
    Tuple3#(Bool,Bit#(12),Bit#(5)) mv_code = decode_MV4(tmp[4:0]); 
	Bit#(5) tmp_boundary = tpl_3(mv_code);
	$display("mv_state_2 tmp = %h",tmp);
	if (tpl_1(mv_code))
	  begin
	    horizontal_mv_data.upd(mv_count,tpl_2(mv_code));
		byte_boundary <= byte_boundary + tmp_boundary[2:0];
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 - tpl_3(mv_code);
		  end 
		else 
		  byte_offset <= byte_offset - tpl_3(mv_code);
        videoSt  <= MV_STATE_3; 
	  end
	else
	  begin
		byte_boundary <= byte_boundary + 4;
	    if (byte_offset < 11) 
	      begin 
	        if (sysState == WAIT) 
	          videoSt  <= MV_STATE_2_1_0; 
		    else 
              videoSt  <= MV_STATE_2_1; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8 -4 ;
			// We are taking off only 4 bits of VLC as they are all 0's if 
			// system reaches this state
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 -4;
		      end 
		    else 
		      byte_offset <= byte_offset -4 ;
            videoSt  <= MV_STATE_2_1; 
          end 
	  end
  endrule

  rule wait_1_cycle67 ((videoSt == MV_STATE_2_1_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= MV_STATE_2_1; 
	$display("wait_1_cycle67 start code reg %h ",start_code_reg); 
  endrule

  rule mv_state_2_1 (videoSt == MV_STATE_2_1);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,7);
    Tuple3#(Bool,Bit#(12),Bit#(5)) mv_code = decode_MV7(tmp[6:0]); 
	Bit#(5) tmp_boundary = tpl_3(mv_code);
	$display("mv_state_2_1 tmp = %h",tmp);
	if (tpl_1(mv_code))
	  begin
	    horizontal_mv_data.upd(mv_count,tpl_2(mv_code));
		byte_boundary <= byte_boundary + tmp_boundary[2:0];
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 - tpl_3(mv_code);
		  end 
		else 
		  byte_offset <= byte_offset - tpl_3(mv_code);
        videoSt  <= MV_STATE_3; 
	  end
	else
	  begin
		byte_boundary <= byte_boundary + 4;
	    if (byte_offset < 9) 
	      begin 
	        if (sysState == WAIT) 
	          videoSt  <= MV_STATE_2_2_0; 
		    else 
              videoSt  <= MV_STATE_2_2; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8 -4 ;
			// We are taking off only 4 bits of VLC as they are all 0's if 
			// system reaches this state
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 -4;
		      end 
		    else 
		      byte_offset <= byte_offset -4 ;
            videoSt  <= MV_STATE_2_2; 
          end 
	  end
  endrule

  rule wait_1_cycle68 ((videoSt == MV_STATE_2_2_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= MV_STATE_2_2; 
	$display("wait_1_cycle68 start code reg %h ",start_code_reg); 
  endrule

  rule mv_state_2_2 (videoSt == MV_STATE_2_2);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,5);
    Tuple3#(Bool,Bit#(12),Bit#(5)) mv_code = decode_MV5(tmp[4:0]); 
	Bit#(5) tmp_boundary = tpl_3(mv_code);
	$display("mv_state_2_2 tmp = %h",tmp);
	if (tpl_1(mv_code))
	  begin
	    horizontal_mv_data.upd(mv_count,tpl_2(mv_code));
		byte_boundary <= byte_boundary + tmp_boundary[2:0];
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 - tpl_3(mv_code);
		  end 
		else 
		  byte_offset <= byte_offset - tpl_3(mv_code);
        videoSt  <= MV_STATE_3; 
	  end
	else
	  $display("Error Error : horizontal mv data not found");
  endrule

  rule mv_state_3 (videoSt == MV_STATE_3);
    if ((vop_fcode_forward != 1) && (horizontal_mv_data.sub(mv_count) != 0))
	  begin
	    if (byte_offset < tmp_vop_fcode_forward ) 
	      begin 
	        if (sysState == WAIT) 
	          videoSt  <= MV_STATE_4_0;
		    else 
              videoSt  <= MV_STATE_4; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8 ;
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 ;
		      end 
		    else 
		      byte_offset <= byte_offset ;
            videoSt  <= MV_STATE_4; 
          end 
	  end
	else
      videoSt  <= MV_STATE_5; 
  endrule

  rule wait_1_cycle69 ((videoSt == MV_STATE_4_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= MV_STATE_4; 
	$display("wait_1_cycle69 start code reg %h ",start_code_reg); 
  endrule

  rule mv_state_4 (videoSt == MV_STATE_4);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,tmp_vop_fcode_forward[3:0]);
	horizontal_mv_residual.upd(mv_count,tmp[5:0]);
	byte_boundary <= byte_boundary + tmp_vop_fcode_forward[2:0];
	if (sysState == START) 
	  begin 
	    sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
	    byte_offset <= byte_offset + 8 - tmp_vop_fcode_forward;
	  end 
    else 
	  byte_offset <= byte_offset - tmp_vop_fcode_forward;
    videoSt  <= MV_STATE_5; 
  endrule

  rule mv_state_5 (videoSt == MV_STATE_5);
	if (byte_offset < 5) 
	  begin 
	    if (sysState == WAIT) 
	      videoSt  <= MV_STATE_6_0;
		else 
          videoSt  <= MV_STATE_6; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset <= byte_offset +8 ;
	  end 
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 ;
		  end 
		else 
		  byte_offset <= byte_offset ;
        videoSt  <= MV_STATE_6; 
      end 
  endrule

  rule wait_1_cycle70 ((videoSt == MV_STATE_6_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= MV_STATE_6; 
	$display("wait_1_cycle70 start code reg %h ",start_code_reg); 
  endrule

  rule mv_state_6 (videoSt == MV_STATE_6);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,5);
    Tuple3#(Bool,Bit#(12),Bit#(5)) mv_code = decode_MV4(tmp[4:0]); 
	Bit#(5) tmp_boundary = tpl_3(mv_code);
	$display("mv_state_6 tmp = %h",tmp);
	if (tpl_1(mv_code))
	  begin
	    vertical_mv_data.upd(mv_count,tpl_2(mv_code));
		byte_boundary <= byte_boundary + tmp_boundary[2:0];
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 - tpl_3(mv_code);
		  end 
		else 
		  byte_offset <= byte_offset - tpl_3(mv_code);
        videoSt  <= MV_STATE_7; 
	  end
	else
	  begin
		byte_boundary <= byte_boundary + 4;
	    if (byte_offset < 11) 
	      begin 
	        if (sysState == WAIT) 
	          videoSt  <= MV_STATE_6_1_0; 
		    else 
              videoSt  <= MV_STATE_6_1; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8 -4 ;
			// We are taking off only 4 bits of VLC as they are all 0's if 
			// system reaches this state
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 -4;
		      end 
		    else 
		      byte_offset <= byte_offset -4 ;
            videoSt  <= MV_STATE_6_1; 
          end 
	  end
  endrule

  rule wait_1_cycle71 ((videoSt == MV_STATE_6_1_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= MV_STATE_6_1; 
	$display("wait_1_cycle71 start code reg %h ",start_code_reg); 
  endrule

  rule mv_state_6_1 (videoSt == MV_STATE_6_1);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,7);
    Tuple3#(Bool,Bit#(12),Bit#(5)) mv_code = decode_MV7(tmp[6:0]); 
	Bit#(5) tmp_boundary = tpl_3(mv_code);
	$display("mb_state_6_1 tmp = %h",tmp);
	if (tpl_1(mv_code))
	  begin
	    vertical_mv_data.upd(mv_count,tpl_2(mv_code));
		byte_boundary <= byte_boundary + tmp_boundary[2:0];
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 - tpl_3(mv_code);
		  end 
		else 
		  byte_offset <= byte_offset - tpl_3(mv_code);
        videoSt  <= MV_STATE_7; 
	  end
	else
	  begin
		byte_boundary <= byte_boundary + 4;
	    if (byte_offset < 9) 
	      begin 
	        if (sysState == WAIT) 
	          videoSt  <= MV_STATE_6_2_0; 
		    else 
              videoSt  <= MV_STATE_6_2; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8 -4 ;
			// We are taking off only 4 bits of VLC as they are all 0's if 
			// system reaches this state
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 -4;
		      end 
		    else 
		      byte_offset <= byte_offset -4 ;
            videoSt  <= MV_STATE_6_2; 
          end 
	  end
  endrule

  rule wait_1_cycle72 ((videoSt == MV_STATE_6_2_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= MV_STATE_6_2; 
	$display("wait_1_cycle72 start code reg %h ",start_code_reg); 
  endrule

  rule mv_state_6_2 (videoSt == MV_STATE_6_2);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,5);
    Tuple3#(Bool,Bit#(12),Bit#(5)) mv_code = decode_MV5(tmp[4:0]); 
	Bit#(5) tmp_boundary = tpl_3(mv_code);
	$display("mb_state_6_2 tmp = %h",tmp);
	if (tpl_1(mv_code))
	  begin
	    vertical_mv_data.upd(mv_count,tpl_2(mv_code));
		byte_boundary <= byte_boundary + tmp_boundary[2:0];
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 - tpl_3(mv_code);
		  end 
		else 
		  byte_offset <= byte_offset - tpl_3(mv_code);
        videoSt  <= MV_STATE_7; 
	  end
	else
	  $display("Error Error : horizontal mv data not found");
  endrule

  rule mv_state_7 (videoSt == MV_STATE_7);
    if ((vop_fcode_forward != 1) && (vertical_mv_data.sub(mv_count) != 0))
	  begin
	    if (byte_offset < tmp_vop_fcode_forward ) 
	      begin 
	        if (sysState == WAIT) 
	          videoSt  <= MV_STATE_8_0;
		    else 
              videoSt  <= MV_STATE_8; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8 ;
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 ;
		      end 
		    else 
		      byte_offset <= byte_offset ;
            videoSt  <= MV_STATE_8; 
          end 
	  end
	else
	  begin
        if (((mbtype == 0) || (mbtype == 1)) && (vop_coding_type == 1)) // Single MV case
	      begin
	        mvp_done <= True;
	        mv_count <= mv_count ;
			update_cnt <= 1;
	      end
	    else
	      begin
	        mvp_done <= False;
	        mv_count <= mv_count + 1;
	      end
        videoSt  <= MB_STATE_10; 
	  end
  endrule

  rule wait_1_cycle73 ((videoSt == MV_STATE_8_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= MV_STATE_8; 
	$display("wait_1_cycle73 start code reg %h ",start_code_reg); 
  endrule

  rule mv_state_8 (videoSt == MV_STATE_8);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,tmp_vop_fcode_forward[3:0]);
	vertical_mv_residual.upd(mv_count,tmp[5:0]);
	byte_boundary <= byte_boundary + tmp_vop_fcode_forward[2:0];
	if (sysState == START) 
	  begin 
	    sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
	    byte_offset <= byte_offset + 8 - tmp_vop_fcode_forward;
	  end 
    else 
	  byte_offset <= byte_offset - tmp_vop_fcode_forward;
    videoSt  <= MB_STATE_10; 
    if (((mbtype == 0) || (mbtype == 1)) && (vop_coding_type == 1)) // Single MV case
	  begin
	    mvp_done <= True;
	    mv_count <= mv_count ;
	  end
	else
	  begin
	    mvp_done <= False;
	    mv_count <= mv_count + 1;
	  end
  endrule

  rule exec_mv_prediction (videoSt == EXEC_MV_PREDICTION);
    let leftblock = -1;
    let topblock = -1;
    let toprightblock = -1; 
	Maybe#(Bit#(12)) mv1_x;
	Maybe#(Bit#(12)) mv1_y;
	Maybe#(Bit#(12)) mv2_x;
	Maybe#(Bit#(12)) mv2_y;
	Maybe#(Bit#(12)) mv3_x;
	Maybe#(Bit#(12)) mv3_y;
	Bit#(12) tmp_mv1_x;
	Bit#(12) tmp_mv1_y;
	Bit#(12) tmp_mv2_x;
	Bit#(12) tmp_mv2_y;
	Bit#(12) tmp_mv3_x;
	Bit#(12) tmp_mv3_y;
	Bit#(12) mvdx;
	Bit#(12) mvdy;
	Bit#(12) tmp_mvx;
	Bit#(12) tmp_mvy;
	Bit#(8)  tmp_mb_width1 = mb_width[7:0];
	Bit#(8)  tmp_address = mv_addr;

	if ((tmp_mb_num_x == 0) || 
	     ((tmp_vop_mb_num_y == 0) && (tmp_mb_num_x != 0) && (tmp_vop_mb_num_x == 0))
	   )
	  begin
	    leftblock = -1;
	    mv1_x = Nothing;
	    mv1_y = Nothing;
		$display("leftblock is -1 cond 1");
	  end
    else 
	  begin
	    if (mv_addr == 0)
		   leftblock = 8*tmp_mb_width1 - 1;
	    else if (mv_addr == (tmp_mb_width1*2))
		   leftblock = 10*tmp_mb_width1 - 1;
	    else if (mv_addr == (tmp_mb_width1*4))
		   leftblock = 2*tmp_mb_width1  - 1;
	    else if (mv_addr == (tmp_mb_width1*6))
		   leftblock = 4*tmp_mb_width1  - 1;
		else
	      leftblock = mv_addr - 1;
		$display("leftblock is cond 2 leftblock = %d",leftblock);
        mv1_x = mvPredBuffer_x.sub(leftblock);
        mv1_y = mvPredBuffer_y.sub(leftblock);
	  end

    if (tmp_vop_mb_num_y == 0)
	  begin
	    topblock = -1;
	    mv2_x = Nothing;
	    mv2_y = Nothing;
		$display("topblock is -1 cond 1 ");
	  end
    else 
	  begin
	    if (tmp_vop_mb_num_y[0] == 1)
		   begin
			 topblock = tmp_address - tmp_mb_width1*2;
		     $display("topblock = %d cond 2 ",topblock);
		   end
		else
		  begin
			 topblock = tmp_address + 6*tmp_mb_width1;
		     $display("topblock = %d cond 3 ",topblock);
		  end
        mv2_x = mvPredBuffer_x.sub(topblock);
        mv2_y = mvPredBuffer_y.sub(topblock);
	  end

    if ((tmp_mb_num_x == (tmp_mb_width-1)) || 
	    ((tmp_vop_mb_num_y == 0) && (tmp_vop_mb_num_x != (tmp_mb_width-1))))
	  begin
	    toprightblock = -1;
	    mv3_x = Nothing;
	    mv3_y = Nothing;
		$display("toprightblock -1 cond 1 ");
	  end
    else 
	  begin
	    if ((mv_addr == (2*tmp_mb_width1 - 2)) && (tmp_vop_mb_num_y == 0))
		  begin
		    toprightblock = 2*(tmp_mb_width1) ;
		    $display("toprightblock = %d cond 2.0 ",toprightblock);
		  end
	    else if ((topblock == (2*tmp_mb_width1 - 2)) || (topblock == (4*tmp_mb_width1 -2)))
		  begin
		    toprightblock = topblock + 2*(tmp_mb_width1) + 2;
		    $display("toprightblock = %d cond 2 ",toprightblock);
		  end
	    else if (topblock == (8*tmp_mb_width1 - 2))
		  begin
		    toprightblock = 0 ;
		    $display("toprightblock = %d cond 3 ",toprightblock);
		  end
	    else if (topblock == (10*tmp_mb_width1 -2))
		  begin
		    toprightblock = 2*tmp_mb_width1 ;
		    $display("toprightblock = %d cond 4 ",toprightblock);
		  end
	    else 
		  begin
		    toprightblock = topblock + 2;
		    $display("toprightblock = %d cond 5 ",toprightblock);
		  end
        mv3_x = mvPredBuffer_x.sub(toprightblock);
        mv3_y = mvPredBuffer_y.sub(toprightblock);
	  end

	 let tmp = mvarith.check_valid(mv1_x,mv1_y,mv2_x,mv2_y,mv3_x,mv3_y);
	 tmp_mv1_x = tpl_1(tmp);
	 tmp_mv1_y = tpl_2(tmp);
	 tmp_mv2_x = tpl_3(tmp);
	 tmp_mv2_y = tpl_4(tmp);
	 tmp_mv3_x = tpl_5(tmp);
	 tmp_mv3_y = tpl_6(tmp);

	 $display("leftblock = %d topblock = %d toprightblock = %d mv_addr = %d",leftblock,topblock,toprightblock,mv_addr);
	 let px = mvarith.median_x(tmp_mv1_x,tmp_mv2_x,tmp_mv3_x);
	 let py = mvarith.median_y(tmp_mv1_y,tmp_mv2_y,tmp_mv3_y);

	 $display("px = %h py = %h ",px,py);
     let r_size = vop_fcode_forward - 1;
	 let f = mvarith.shift_left(r_size);
	 let high = mvarith.get_high(r_size);
	 let low = mvarith.get_low(r_size);
	 let range = (high + 1) << 1 ;

     $display("low %h high %h range %h",low,high,range);

     mvdx = mvarith.getMVDx(horizontal_mv_data.sub(0),zeroExtend(horizontal_mv_residual.sub(0)),f,r_size);
     mvdy = mvarith.getMVDy(vertical_mv_data.sub(0),zeroExtend(vertical_mv_residual.sub(0)),f,r_size);

	 tmp_mvx = mvarith.saturate_mvx(px+mvdx,high,low,range);
	 tmp_mvy = mvarith.saturate_mvy(py+mvdy,high,low,range);
	 $display("writing mvPredBuffer addr = %d datax = %h datay = %h",mv_addr,tmp_mvx,tmp_mvy);
     mvPredBuffer_x.upd(mv_addr,Just(tmp_mvx));
     mvPredBuffer_y.upd(mv_addr,Just(tmp_mvy));
	 update_cnt <= update_cnt + 1;
	 mvx <= {tmp_mvx,tmp_mvx,tmp_mvx,tmp_mvx};
	 mvy <= {tmp_mvy,tmp_mvy,tmp_mvy,tmp_mvy};
	 if (mbtype != 2)
	   videoSt <= EXEC_MV_PREDICTION1;
	 else
	   begin
	     videoSt <= EXEC_4MV_PREDICTION;
		 $display("4 MV condition found");
	   end
  endrule

  rule exec_mv_prediction1 (videoSt == EXEC_MV_PREDICTION1);
	 if (update_cnt != 4)
	   begin
	     $display("writing mvPredBuffer addr = %d datax = %h datay = %h",mv_addr,mvx[11:0],mvy[11:0]);
         mvPredBuffer_x.upd(mv_addr,Just(mvx[11:0]));
         mvPredBuffer_y.upd(mv_addr,Just(mvy[11:0]));
		 update_cnt <= update_cnt + 1;
	   end
	 else
	   begin
          mbheaderfifo.enq(tuple7(mbNum,not_coded,cbpy,cbpc,isInter,mvx,mvy));
		  update_cnt <= 0;
	      videoSt <= MB_BLK_STATE;
	   end
  endrule

  rule exec_4mv_prediction (videoSt == EXEC_4MV_PREDICTION);
    let leftblock = -1;
    let topblock = -1;
    let toprightblock = -1; 
	Maybe#(Bit#(12)) mv1_x;
	Maybe#(Bit#(12)) mv1_y;
	Maybe#(Bit#(12)) mv2_x;
	Maybe#(Bit#(12)) mv2_y;
	Maybe#(Bit#(12)) mv3_x;
	Maybe#(Bit#(12)) mv3_y;
	Bit#(12) tmp_mv1_x;
	Bit#(12) tmp_mv1_y;
	Bit#(12) tmp_mv2_x;
	Bit#(12) tmp_mv2_y;
	Bit#(12) tmp_mv3_x;
	Bit#(12) tmp_mv3_y;
	Bit#(12) mvdx;
	Bit#(12) mvdy;
	Bit#(12) tmp_mvx;
	Bit#(12) tmp_mvy;
	Bit#(8)  tmp_mb_width1 = mb_width[7:0];
	Bit#(8)  tmp_address = mv_addr;

	leftblock = mv_addr - 1;
	$display("leftblock in exec_4mv_prediction is cond 1 leftblock = %d",leftblock);
    mv1_x = mvPredBuffer_x.sub(leftblock);
    mv1_y = mvPredBuffer_y.sub(leftblock);

    if (tmp_vop_mb_num_y == 0)
	  begin
	    topblock = -1;
	    mv2_x = Nothing;
	    mv2_y = Nothing;
		$display("topblock in exec_4mv_prediction is -1 cond 1 ");
	  end
    else 
	  begin
	    if (tmp_vop_mb_num_y[0] == 1)
		   begin
			 topblock = tmp_address - tmp_mb_width1*2;
		     $display("topblock = %d cond 2 exec_4mv_prediction ",topblock);
		   end
		else
		  begin
			 topblock = tmp_address + 8*tmp_mb_width1;
		     $display("topblock = %d cond 3 exec_4mv_prediction ",topblock);
		  end
        mv2_x = mvPredBuffer_x.sub(topblock);
        mv2_y = mvPredBuffer_y.sub(topblock);
	  end

    if ((tmp_mb_num_x == (tmp_mb_width-1)) || 
	    ((tmp_vop_mb_num_y == 0) && (tmp_vop_mb_num_x != (tmp_mb_width-1))))
	  begin
	    toprightblock = -1;
	    mv3_x = Nothing;
	    mv3_y = Nothing;
		$display("toprightblock -1 cond 1 ");
	  end
    else 
	  begin
	    if ((mv_addr == (2*tmp_mb_width1 - 1)) && (tmp_vop_mb_num_y == 0))
		  begin
		    toprightblock = 2*(tmp_mb_width1) ;
		    $display("toprightblock = %d cond 2.0 ",toprightblock);
		  end
	    else if ((topblock == (2*tmp_mb_width1 - 1)) || (topblock == (4*tmp_mb_width1 -1)))
		  begin
		    toprightblock = topblock + 2*(tmp_mb_width1) + 1;
		    $display("toprightblock = %d cond 2 ",toprightblock);
		  end
	    else if (topblock == (8*tmp_mb_width1 - 1))
		  begin
		    toprightblock = 0 ;
		    $display("toprightblock = %d cond 3 ",toprightblock);
		  end
	    else if (topblock == (10*tmp_mb_width1 -1))
		  begin
		    toprightblock = 2*tmp_mb_width1 ;
		    $display("toprightblock = %d cond 4 ",toprightblock);
		  end
	    else 
		  begin
		    toprightblock = topblock + 1;
		    $display("toprightblock = %d cond 5 ",toprightblock);
		  end
        mv3_x = mvPredBuffer_x.sub(toprightblock);
        mv3_y = mvPredBuffer_y.sub(toprightblock);
	  end

	 let tmp = mvarith.check_valid(mv1_x,mv1_y,mv2_x,mv2_y,mv3_x,mv3_y);
	 tmp_mv1_x = tpl_1(tmp);
	 tmp_mv1_y = tpl_2(tmp);
	 tmp_mv2_x = tpl_3(tmp);
	 tmp_mv2_y = tpl_4(tmp);
	 tmp_mv3_x = tpl_5(tmp);
	 tmp_mv3_y = tpl_6(tmp);
    
	 let px = mvarith.median_x(tmp_mv1_x,tmp_mv2_x,tmp_mv3_x);
	 let py = mvarith.median_y(tmp_mv1_y,tmp_mv2_y,tmp_mv3_y);

     let r_size = vop_fcode_forward - 1;
	 let f = mvarith.shift_left(r_size);
	 let high = mvarith.get_high(r_size);
	 let low = mvarith.get_low(r_size);
	 let range = (high + 1) << 1 ;

     $display("low %h high %h range %h",low,high,range);

     mvdx = mvarith.getMVDx(horizontal_mv_data.sub(1),zeroExtend(horizontal_mv_residual.sub(1)),f,r_size);
     mvdy = mvarith.getMVDy(vertical_mv_data.sub(1),zeroExtend(vertical_mv_residual.sub(1)),f,r_size);

	 tmp_mvx = mvarith.saturate_mvx(px+mvdx,high,low,range);
	 tmp_mvy = mvarith.saturate_mvy(py+mvdy,high,low,range);
     mvPredBuffer_x.upd(mv_addr,Just(tmp_mvx));
     mvPredBuffer_y.upd(mv_addr,Just(tmp_mvy));
	 update_cnt <= update_cnt + 1;
	 mvx <= {mvx[47:36],tmp_mvx,tmp_mvx,tmp_mvx};
	 mvy <= {mvy[47:36],tmp_mvy,tmp_mvy,tmp_mvy};
     videoSt <= EXEC_4MV_PREDICTION1;
  endrule

  rule exec_4mv_prediction1 (videoSt == EXEC_4MV_PREDICTION1);
    let leftblock = -1;
    let topblock = -1;
    let toprightblock = -1; 
	Maybe#(Bit#(12)) mv1_x;
	Maybe#(Bit#(12)) mv1_y;
	Maybe#(Bit#(12)) mv2_x;
	Maybe#(Bit#(12)) mv2_y;
	Maybe#(Bit#(12)) mv3_x;
	Maybe#(Bit#(12)) mv3_y;
	Bit#(12) tmp_mv1_x;
	Bit#(12) tmp_mv1_y;
	Bit#(12) tmp_mv2_x;
	Bit#(12) tmp_mv2_y;
	Bit#(12) tmp_mv3_x;
	Bit#(12) tmp_mv3_y;
	Bit#(12) mvdx;
	Bit#(12) mvdy;
	Bit#(12) tmp_mvx;
	Bit#(12) tmp_mvy;
	Bit#(8)  tmp_mb_width1 = mb_width[7:0];
	Bit#(8)  tmp_address = mv_addr;

	if ((tmp_mb_num_x == 0) || 
	     ((tmp_vop_mb_num_y == 0) && (tmp_mb_num_x != 0) && (tmp_vop_mb_num_x == 0))
	   )
	  begin
	    leftblock = -1;
	    mv1_x = Nothing;
	    mv1_y = Nothing;
		$display("leftblock is -1 cond 1");
	  end
    else 
	  begin
	    if (mv_addr == 0)
		   leftblock = 8*tmp_mb_width1 - 1;
	    else if (mv_addr == (tmp_mb_width1*2))
		   leftblock = 10*tmp_mb_width1 - 1;
	    else if (mv_addr == (tmp_mb_width1*4))
		   leftblock = 2*tmp_mb_width1  - 1;
	    else if (mv_addr == (tmp_mb_width1*8))
		   leftblock = 4*tmp_mb_width1  - 1;
		else
	      leftblock = mv_addr - 1;
		$display("leftblock is cond 2 leftblock = %d",leftblock);
        mv1_x = mvPredBuffer_x.sub(leftblock);
        mv1_y = mvPredBuffer_y.sub(leftblock);
	  end

    topblock = tmp_address - tmp_mb_width1*2;
    $display("topblock is cond 1 topblock = %d",topblock);
    mv2_x = mvPredBuffer_x.sub(topblock);
    mv2_y = mvPredBuffer_y.sub(topblock);

    toprightblock = topblock + 1;
    mv3_x = mvPredBuffer_x.sub(toprightblock);
    mv3_y = mvPredBuffer_y.sub(toprightblock);

	 let tmp = mvarith.check_valid(mv1_x,mv1_y,mv2_x,mv2_y,mv3_x,mv3_y);
	 tmp_mv1_x = tpl_1(tmp);
	 tmp_mv1_y = tpl_2(tmp);
	 tmp_mv2_x = tpl_3(tmp);
	 tmp_mv2_y = tpl_4(tmp);
	 tmp_mv3_x = tpl_5(tmp);
	 tmp_mv3_y = tpl_6(tmp);
    
	let px = mvarith.median_x(tmp_mv1_x,tmp_mv2_x,tmp_mv3_x);
	let py = mvarith.median_y(tmp_mv1_y,tmp_mv2_y,tmp_mv3_y);

    let r_size = vop_fcode_forward - 1;
	let f = mvarith.shift_left(r_size);
	let high = mvarith.get_high(r_size);
	let low = mvarith.get_low(r_size);
	let range = (high + 1) << 1 ;

    $display("low %h high %h range %h",low,high,range);

    mvdx = mvarith.getMVDx(horizontal_mv_data.sub(2),zeroExtend(horizontal_mv_residual.sub(2)),f,r_size);
    mvdy = mvarith.getMVDy(vertical_mv_data.sub(2),zeroExtend(vertical_mv_residual.sub(2)),f,r_size);

	tmp_mvx = mvarith.saturate_mvx(px+mvdx,high,low,range);
	tmp_mvy = mvarith.saturate_mvy(py+mvdy,high,low,range);
    mvPredBuffer_x.upd(mv_addr,Just(tmp_mvx));
    mvPredBuffer_y.upd(mv_addr,Just(tmp_mvy));
	update_cnt <= update_cnt + 1;
	mvx <= {mvx[47:24],tmp_mvx,tmp_mvx};
	mvy <= {mvy[47:24],tmp_mvy,tmp_mvy};
    videoSt <= EXEC_4MV_PREDICTION2;
  endrule

  rule exec_4mv_prediction2 (videoSt == EXEC_4MV_PREDICTION2);
    let leftblock = -1;
    let topblock = -1;
    let toprightblock = -1; 
	Maybe#(Bit#(12)) mv1_x;
	Maybe#(Bit#(12)) mv1_y;
	Maybe#(Bit#(12)) mv2_x;
	Maybe#(Bit#(12)) mv2_y;
	Maybe#(Bit#(12)) mv3_x;
	Maybe#(Bit#(12)) mv3_y;
	Bit#(12) tmp_mv1_x;
	Bit#(12) tmp_mv1_y;
	Bit#(12) tmp_mv2_x;
	Bit#(12) tmp_mv2_y;
	Bit#(12) tmp_mv3_x;
	Bit#(12) tmp_mv3_y;
	Bit#(12) mvdx;
	Bit#(12) mvdy;
	Bit#(12) tmp_mvx;
	Bit#(12) tmp_mvy;
	Bit#(8)  tmp_mb_width1 = mb_width[7:0];
	Bit#(8)  tmp_address = mv_addr;

	leftblock = mv_addr - 1;
	$display("leftblock is cond 2 leftblock = %d",leftblock);
    mv1_x = mvPredBuffer_x.sub(leftblock);
    mv1_y = mvPredBuffer_y.sub(leftblock);

    topblock = tmp_address - tmp_mb_width1*2 - 1;
    $display("topblock is cond 1 topblock = %d",topblock);
    mv2_x = mvPredBuffer_x.sub(topblock);
    mv2_y = mvPredBuffer_y.sub(topblock);

    toprightblock = topblock + 1;
    mv3_x = mvPredBuffer_x.sub(toprightblock);
    mv3_y = mvPredBuffer_y.sub(toprightblock);

	 let tmp = mvarith.check_valid(mv1_x,mv1_y,mv2_x,mv2_y,mv3_x,mv3_y);
	 tmp_mv1_x = tpl_1(tmp);
	 tmp_mv1_y = tpl_2(tmp);
	 tmp_mv2_x = tpl_3(tmp);
	 tmp_mv2_y = tpl_4(tmp);
	 tmp_mv3_x = tpl_5(tmp);
	 tmp_mv3_y = tpl_6(tmp);
    
	let px = mvarith.median_x(tmp_mv1_x,tmp_mv2_x,tmp_mv3_x);
	let py = mvarith.median_y(tmp_mv1_y,tmp_mv2_y,tmp_mv3_y);

    let r_size = vop_fcode_forward - 1;
	let f = mvarith.shift_left(r_size);
	let high = mvarith.get_high(r_size);
	let low = mvarith.get_low(r_size);
	let range = (high + 1) << 1 ;

    $display("low %h high %h range %h",low,high,range);

    mvdx = mvarith.getMVDx(horizontal_mv_data.sub(3),zeroExtend(horizontal_mv_residual.sub(3)),f,r_size);
    mvdy = mvarith.getMVDy(vertical_mv_data.sub(3),zeroExtend(vertical_mv_residual.sub(3)),f,r_size);

	tmp_mvx = mvarith.saturate_mvx(px+mvdx,high,low,range);
	tmp_mvy = mvarith.saturate_mvy(py+mvdy,high,low,range);
    mvPredBuffer_x.upd(mv_addr,Just(tmp_mvx));
    mvPredBuffer_y.upd(mv_addr,Just(tmp_mvy));
	update_cnt <= update_cnt + 1;
	mvx <= {mvx[47:12],tmp_mvx};
	mvy <= {mvy[47:12],tmp_mvy};
    videoSt <= EXEC_4MV_PREDICTION3;
  endrule

  rule exec_4mv_prediction3 (videoSt == EXEC_4MV_PREDICTION3);
    mbheaderfifo.enq(tuple7(mbNum,not_coded,cbpy,cbpc,isInter,mvx,mvy));
	update_cnt <= 0;
	videoSt <= MB_BLK_STATE;
  endrule

endrules;
return r;
endfunction
// *************************************************
// End of block6
// *************************************************

// *************************************************
// Start of block7
// *************************************************
function Rules create_block7 ();
 Rules r = rules

  rule mb_blk_state (videoSt == MB_BLK_STATE);
    last <= False; 
	dct_coeff_cnt <= 0;

	if (isIntra)
	  begin
	    if (blkBuffer.busy == False)
	      begin
            $display("############  block count = %d mb_cnt_x = %d mb_cnt_y = %d",blk_cnt,mb_num_x,mb_num_y);
		    if (blk_cnt != 0)
		      begin
		        blkBuffer.sent_output_data(1'b1);
		      end
            videoSt  <= MB_BLK_STATE_00; 
	      end
	    else
          videoSt  <= MB_BLK_STATE_00_0; 
	  end
	else
	  begin
		if (blk_cnt != 0)
		  begin
	        if  (pattern_code_d && pattern_code)
              videoSt  <= MB_BLK_STATE_00_0; 
		    else if (!pattern_code_d && pattern_code)
		      begin
                videoSt  <= MB_BLK_STATE_00; 
                $display("############  block count = %d mb_cnt_x = %d mb_cnt_y = %d",blk_cnt,mb_num_x,mb_num_y);
		      end
		    else if (pattern_code_d && !pattern_code)
		      begin
			    wait_cnt <= wait_cnt + 1;
                videoSt  <= WAIT64; 
                $display("############  block count = %d mb_cnt_x = %d mb_cnt_y = %d",blk_cnt,mb_num_x,mb_num_y);
		      end
		    else
		      begin
                videoSt  <= JUST_WAIT64; 
                $display("############  block count = %d mb_cnt_x = %d mb_cnt_y = %d",blk_cnt,mb_num_x,mb_num_y);
		      end
		  end
	   else
	     begin
		   $display("New MB has started");
           $display("############  block count = %d mb_cnt_x = %d mb_cnt_y = %d",blk_cnt,mb_num_x,mb_num_y);
           videoSt  <= MB_BLK_STATE_00_0; 
		 end
	  end
  endrule

  rule wait64 (videoSt == WAIT64);
     if (wait_cnt == 63)
	    begin
          videoSt  <= MB_BLK_STATE_12; 
		  wait_cnt <= 0;
	    end
	 else if (wait_cnt == 1)
		begin
		  if (blkBuffer.busy == False)
			begin
		      blkBuffer.sent_output_data(1'b1);
		      wait_cnt <= 2;
			end
		end
	 else if (wait_cnt == 2)
		begin
          $display("clear signal");
	      blkBuffer.clear_d(1'b1); // send clear signal
		  wait_cnt <= 3;
		end
     else
		wait_cnt <= wait_cnt + 1;
  endrule

  rule justwait64 (videoSt == JUST_WAIT64);
    if (wait_cnt == 63)
	  begin
        videoSt  <= MB_BLK_STATE_12; 
		wait_cnt <= 0;
	  end
    else
	  wait_cnt <= wait_cnt + 1;
  endrule

  rule mb_blk_state_00_0 (videoSt == MB_BLK_STATE_00_0);
	if (blkBuffer.busy == False)
	  begin
        $display("############  block count = %d mb_cnt_x = %d mb_cnt_y = %d",blk_cnt,mb_num_x,mb_num_y);
		if (blk_cnt !=0)
		  blkBuffer.sent_output_data(1'b1);
        videoSt  <= MB_BLK_STATE_00; 
	  end
  endrule

  rule mb_blk_state_00 (videoSt == MB_BLK_STATE_00);
    $display("clear signal");
	blkBuffer.clear_d(1'b1); // send clear signal
	if ((data_partitioned == 0) && isIntra && (not_coded == 0))
       videoSt  <= MB_BLK_STATE_0; 
	else 
       videoSt  <= MB_BLK_STATE_12; 
  endrule

  rule mb_blk_state_0 (videoSt == MB_BLK_STATE_0);
	if (short_video_header)
	  begin
	    if (byte_offset < 8) 
	      begin 
	        if (sysState == WAIT) 
              videoSt  <= MB_BLK_STATE_1_0; 
		    else 
              videoSt  <= MB_BLK_STATE_1; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8 ;
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 ;
		      end 
		    else 
		      byte_offset <= byte_offset ;
            videoSt  <= MB_BLK_STATE_1; 
          end 
	  end
	else if (use_intra_dc_vlc)
	  begin
	    dct_coeff_cnt <= 1;
	    if (blk_cnt < 4)
	       begin
	         if (byte_offset < 4) 
	           begin 
	             if (sysState == WAIT) 
                   videoSt  <= MB_BLK_STATE_2_0; 
		         else 
                   videoSt  <= MB_BLK_STATE_2; 
		         sysState <= START; 
		         vd_rd_reg <= 1'b1; 
		         byte_offset <= byte_offset +8 ;
	           end 
	         else
               begin 
	             if (sysState == START) 
		           begin 
			         sysState <= WAIT; 
			         vd_rd_reg <= 1'b0; 
		             byte_offset <= byte_offset +8 ;
		           end 
		         else 
		           byte_offset <= byte_offset ;
                 videoSt  <= MB_BLK_STATE_2; 
               end 
	       end
		else
	       begin
	         if (byte_offset < 4) 
	           begin 
	             if (sysState == WAIT) 
                   videoSt  <= MB_BLK_STATE_7_0; 
		         else 
                   videoSt  <= MB_BLK_STATE_7; 
		         sysState <= START; 
		         vd_rd_reg <= 1'b1; 
		         byte_offset <= byte_offset +8 ;
	           end 
	         else
               begin 
	             if (sysState == START) 
		           begin 
			         sysState <= WAIT; 
			         vd_rd_reg <= 1'b0; 
		             byte_offset <= byte_offset +8 ;
		           end 
		         else 
		           byte_offset <= byte_offset ;
                 videoSt  <= MB_BLK_STATE_7; 
               end 
	       end
	  end
	else
      videoSt  <= MB_BLK_STATE_12; 
  endrule

  rule wait_1_cycle74 ((videoSt == MB_BLK_STATE_1_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= MB_BLK_STATE_1; 
	$display("wait_1_cycle74 start code reg %h ",start_code_reg); 
  endrule

  rule  mb_blk_state_1(videoSt == MB_BLK_STATE_1);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	intra_dc_coefficient <= tmp[7:0];
	if (sysState == START) 
      begin 
		sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
		byte_offset <= byte_offset ;
	  end 
    else 
	  byte_offset <= byte_offset -8 ;
    videoSt  <= MB_BLK_STATE_10; 
  endrule

  rule wait_1_cycle75 ((videoSt == MB_BLK_STATE_2_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= MB_BLK_STATE_2; 
	$display("wait_1_cycle75 start code reg %h ",start_code_reg); 
  endrule

  rule mb_blk_state_2 (videoSt == MB_BLK_STATE_2);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,4);
    Tuple3#(Bool,Bit#(4),Bit#(5)) dct_dc_size_luma_code = decode_dct_dc_size_luma4(tmp[3:0]); 
	Bit#(5) tmp_boundary = tpl_3(dct_dc_size_luma_code);
	$display("mb_blk_state_2 tmp = %h",tmp);
	if (tpl_1(dct_dc_size_luma_code))
	  begin
	    dct_dc_size_luma <= tpl_2(dct_dc_size_luma_code);
		byte_boundary <= byte_boundary + tmp_boundary[2:0];
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 - tpl_3(dct_dc_size_luma_code);
		  end 
		else 
		  byte_offset <= byte_offset - tpl_3(dct_dc_size_luma_code);
        videoSt  <= MB_BLK_STATE_3; 
	  end
	else
	  begin
		byte_boundary <= byte_boundary + 4;
	    if (byte_offset < 11) 
	      begin 
	        if (sysState == WAIT) 
	          videoSt  <= MB_BLK_STATE_2_1_0; 
		    else 
              videoSt  <= MB_BLK_STATE_2_1; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8 -4 ;
			// We are taking off only 4 bits of VLC as they are all 0's if 
			// system reaches this state
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 -4;
		      end 
		    else 
		      byte_offset <= byte_offset -4 ;
            videoSt  <= MB_BLK_STATE_2_1; 
          end 
	  end
  endrule

  rule wait_1_cycle75_0 ((videoSt == MB_BLK_STATE_2_1_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= MB_BLK_STATE_2_1; 
	$display("wait_1_cycle75_0 start code reg %h byte_offset = %d",start_code_reg,byte_offset); 
  endrule

  rule mb_blk_state_2_1 (videoSt == MB_BLK_STATE_2_1);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,7);
    Tuple3#(Bool,Bit#(4),Bit#(5)) dct_dc_size_luma_code = decode_dct_dc_size_luma7(tmp[6:0]); 
	Bit#(5) tmp_boundary = tpl_3(dct_dc_size_luma_code);
	$display("mb_blk_state_2_1 tmp = %h start_code_reg = %h byte_offset =%d",tmp,start_code_reg,byte_offset);
	if (tpl_1(dct_dc_size_luma_code))
	  begin
	    dct_dc_size_luma <= tpl_2(dct_dc_size_luma_code);
		byte_boundary <= byte_boundary + tmp_boundary[2:0];
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 - tpl_3(dct_dc_size_luma_code);
		  end 
		else 
		  byte_offset <= byte_offset - tpl_3(dct_dc_size_luma_code);
        videoSt  <= MB_BLK_STATE_3; 
	  end
	else
	  $display("Error Error :  dct_dc_size_luma not found");
  endrule

  rule mb_blk_state_3 (videoSt == MB_BLK_STATE_3);
    if (dct_dc_size_luma != 0)
	  begin
	    if (byte_offset < zeroExtend(dct_dc_size_luma)) 
	      begin 
	        if (sysState == WAIT) 
	          videoSt  <= MB_BLK_STATE_4_0;
		    else 
              videoSt  <= MB_BLK_STATE_4; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8 ;
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 ;
		      end 
		    else 
		      byte_offset <= byte_offset ;
            videoSt  <= MB_BLK_STATE_4; 
          end 
	  end
	else
      videoSt  <= MB_BLK_STATE_12; 
  endrule

  rule wait_1_cycle76 ((videoSt == MB_BLK_STATE_4_0) && (vd_valid.wget == Just(1))) ; 
	if (byte_offset > zeroExtend(dct_dc_size_luma))
      videoSt <= MB_BLK_STATE_4; 
	else
      videoSt <= MB_BLK_STATE_4_0; 
	$display("wait_1_cycle76 start code reg %h ",start_code_reg); 
  endrule

  rule mb_blk_state_4 (videoSt == MB_BLK_STATE_4);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,zeroExtend(dct_dc_size_luma));
	//Bit#(12) scaled_dc_ref_value = division.div_func(acdcPredBuffer.sub(predicted_address),dc_scaler);
	//Bit#(12) scaled_dc_ref_value = acdcPredBuffer.sub(predicted_address);
	Bit#(12) tmp_differential_dc;
	//Bit#(12) dc_coeff;
      case(dct_dc_size_luma)
	    4'd0 : tmp_differential_dc = 12'd0;
		4'd1 : tmp_differential_dc = (tmp[0] == 1) ? 12'd1 : 12'hfff;
		4'd2 : tmp_differential_dc = (tmp[1] == 1) ? zeroExtend(tmp[1:0]) : (~zeroExtend(~tmp[1:0]) + 1);
		4'd3 : tmp_differential_dc = (tmp[2] == 1) ? zeroExtend(tmp[2:0]) : (~zeroExtend(~tmp[2:0]) + 1);
		4'd4 : tmp_differential_dc = (tmp[3] == 1) ? zeroExtend(tmp[3:0]) : (~zeroExtend(~tmp[3:0]) + 1);
		4'd5 : tmp_differential_dc = (tmp[4] == 1) ? zeroExtend(tmp[4:0]) : (~zeroExtend(~tmp[4:0]) + 1);
		4'd6 : tmp_differential_dc = (tmp[5] == 1) ? zeroExtend(tmp[5:0]) : (~zeroExtend(~tmp[5:0]) + 1);
		4'd7 : tmp_differential_dc = (tmp[6] == 1) ? zeroExtend(tmp[6:0]) : (~zeroExtend(~tmp[6:0]) + 1);
		4'd8 : tmp_differential_dc = (tmp[7] == 1) ? zeroExtend(tmp[7:0]) : (~zeroExtend(~tmp[7:0]) + 1);
		4'd9 : tmp_differential_dc = (tmp[8] == 1) ? zeroExtend(tmp[8:0]) : (~zeroExtend(~tmp[8:0]) + 1);
		4'd10: tmp_differential_dc = (tmp[9] == 1) ? zeroExtend(tmp[9:0]) : (~zeroExtend(~tmp[9:0]) + 1);
		4'd11: tmp_differential_dc = (tmp[10] == 1) ? zeroExtend(tmp[10:0]) : (~zeroExtend(~tmp[10:0]) + 1);
	  default: tmp_differential_dc = 0; 
     endcase
	 // Do I need to check if its intra and short_video_header is 0 ??
	 //dc_coeff = (tmp_differential_dc + scaled_dc_ref_value) * signExtend(dc_scaler);
	 //blkBuffer.write_d(tuple3(1,0,dc_coeff));
	 //acdcPredBuffer.upd(current_address_luma,dc_coeff);
	 // commenting above as ac/dc prediction is done for intra blocks
	 // anyway and these values only come for them
	 // so dc prediction is done at one place in EXEC_ACDC_PREDICTION 
	 // state
	 blkBuffer.write_d(tuple3(1,0,tmp_differential_dc));
	 acdcPredBuffer.upd(current_address,Just(signExtend(tmp_differential_dc)));
	 $display("writing acdcPredBuffer addr = %d tmp_differential_dc = %h",current_address,tmp_differential_dc);
	 //dct_coeff_cnt <= 0;
	 dct_coeff_cnt <= 1;
	 byte_boundary <= byte_boundary + dct_dc_size_luma[2:0];
	 if (sysState == START) 
	  begin 
	    sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
		byte_offset <= byte_offset +8 - zeroExtend(dct_dc_size_luma);
	  end 
	else 
	  byte_offset <= byte_offset - zeroExtend(dct_dc_size_luma);
    videoSt <= MB_BLK_STATE_5; 
  endrule

  rule mb_blk_state_5 (videoSt == MB_BLK_STATE_5);
    if (dct_dc_size_luma > 8)
	  begin
	    if (byte_offset < 1) 
	      begin 
	        if (sysState == WAIT) 
	          videoSt  <= MB_BLK_STATE_6_0;
		    else 
              videoSt  <= MB_BLK_STATE_6; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8 ;
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 ;
		      end 
		    else 
		      byte_offset <= byte_offset ;
            videoSt  <= MB_BLK_STATE_6; 
          end 
	  end
	else
      videoSt  <= MB_BLK_STATE_12; 
  endrule

  rule wait_1_cycle77 ((videoSt == MB_BLK_STATE_6_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= MB_BLK_STATE_6; 
	$display("wait_1_cycle77 start code reg %h ",start_code_reg); 
  endrule

  rule mb_blk_state_6 (videoSt == MB_BLK_STATE_6);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	marker_bit <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	 if (sysState == START) 
	  begin 
	    sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
		byte_offset <= byte_offset +8 - 1;
	  end 
	else 
	  byte_offset <= byte_offset - 1;
    videoSt <= MB_BLK_STATE_12;  
  endrule

  rule wait_1_cycle77_1 ((videoSt == MB_BLK_STATE_7_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= MB_BLK_STATE_7; 
	$display("wait_1_cycle77_1 start code reg %h ",start_code_reg); 
  endrule

  rule mb_blk_state_7 (videoSt == MB_BLK_STATE_7);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,4);
    Tuple3#(Bool,Bit#(4),Bit#(5)) dct_dc_size_chroma_code = decode_dct_dc_size_chroma4(tmp[3:0]); 
	Bit#(5) tmp_boundary = tpl_3(dct_dc_size_chroma_code);
	$display("mb_blk_state_7 tmp = %h",tmp);
	if (tpl_1(dct_dc_size_chroma_code))
	  begin
	    dct_dc_size_chroma <= tpl_2(dct_dc_size_chroma_code);
		byte_boundary <= byte_boundary + tmp_boundary[2:0];
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 - tpl_3(dct_dc_size_chroma_code);
		  end 
		else 
		  byte_offset <= byte_offset - tpl_3(dct_dc_size_chroma_code);
        videoSt  <= MB_BLK_STATE_8; 
	  end
	else
	  begin
		byte_boundary <= byte_boundary + 4;
	    if (byte_offset < 12) 
	      begin 
	        if (sysState == WAIT) 
	          videoSt  <= MB_BLK_STATE_7_1_0; 
		    else 
              videoSt  <= MB_BLK_STATE_7_1; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8 -4 ;
			// We are taking off only 4 bits of VLC as they are all 0's if 
			// system reaches this state
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 -4;
		      end 
		    else 
		      byte_offset <= byte_offset -4 ;
            videoSt  <= MB_BLK_STATE_7_1; 
          end 
	  end
  endrule

  rule wait_1_cycle77_1_0 ((videoSt == MB_BLK_STATE_7_1_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= MB_BLK_STATE_7_1; 
	$display("wait_1_cycle77_1_0 start code reg %h ",start_code_reg); 
  endrule

  rule mb_blk_state_7_1 (videoSt == MB_BLK_STATE_7_1);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
    Tuple3#(Bool,Bit#(4),Bit#(5)) dct_dc_size_chroma_code = decode_dct_dc_size_chroma8(tmp[7:0]); 
	Bit#(5) tmp_boundary = tpl_3(dct_dc_size_chroma_code);
	$display("mb_blk_state_7_1 tmp = %h",tmp);
	if (tpl_1(dct_dc_size_chroma_code))
	  begin
	    dct_dc_size_chroma <= tpl_2(dct_dc_size_chroma_code);
		byte_boundary <= byte_boundary + tmp_boundary[2:0];
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset +8 - tpl_3(dct_dc_size_chroma_code);
		  end 
		else 
		  byte_offset <= byte_offset - tpl_3(dct_dc_size_chroma_code);
        videoSt  <= MB_BLK_STATE_8; 
	  end
	else
	  $display("Error Error :  dct_dc_size_chroma not found");
  endrule

  rule mb_blk_state_8 (videoSt == MB_BLK_STATE_8);
    if (dct_dc_size_chroma != 0)
	  begin
	    if (byte_offset < zeroExtend(dct_dc_size_chroma)) 
	      begin 
	        if (sysState == WAIT) 
	          videoSt  <= MB_BLK_STATE_9_0;
		    else 
              videoSt  <= MB_BLK_STATE_9; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8 ;
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 ;
		      end 
		    else 
		      byte_offset <= byte_offset ;
            videoSt  <= MB_BLK_STATE_9; 
          end 
	  end
	else
      videoSt  <= MB_BLK_STATE_12; 
  endrule

  rule wait_1_cycle78 ((videoSt == MB_BLK_STATE_9_0) && (vd_valid.wget == Just(1))) ; 
	if (byte_offset > zeroExtend(dct_dc_size_chroma))
      videoSt <= MB_BLK_STATE_9; 
	else
      videoSt <= MB_BLK_STATE_9_0; 
	$display("wait_1_cycle78 start code reg %h ",start_code_reg); 
  endrule

  rule mb_blk_state_9 (videoSt == MB_BLK_STATE_9);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,zeroExtend(dct_dc_size_chroma));
	//Bit#(12) scaled_dc_ref_value = division.div_func(acdcPredBuffer.sub(predicted_address),dc_scaler);
	Bit#(12) tmp_differential_dc;
	//Bit#(12) dc_coeff;
	//Bit#(12) scaled_dc_ref_value = acdcPredBuffer.sub(predicted_address);
      case(dct_dc_size_chroma)
	    4'd0 : tmp_differential_dc = 12'd0;
		4'd1 : tmp_differential_dc = (tmp[0] == 1) ? 12'd1 : 12'hfff;
		4'd2 : tmp_differential_dc = (tmp[1] == 1) ? zeroExtend(tmp[1:0]) : (~zeroExtend(~tmp[1:0]) + 1);
		4'd3 : tmp_differential_dc = (tmp[2] == 1) ? zeroExtend(tmp[2:0]) : (~zeroExtend(~tmp[2:0]) + 1);
		4'd4 : tmp_differential_dc = (tmp[3] == 1) ? zeroExtend(tmp[3:0]) : (~zeroExtend(~tmp[3:0]) + 1);
		4'd5 : tmp_differential_dc = (tmp[4] == 1) ? zeroExtend(tmp[4:0]) : (~zeroExtend(~tmp[4:0]) + 1);
		4'd6 : tmp_differential_dc = (tmp[5] == 1) ? zeroExtend(tmp[5:0]) : (~zeroExtend(~tmp[5:0]) + 1);
		4'd7 : tmp_differential_dc = (tmp[6] == 1) ? zeroExtend(tmp[6:0]) : (~zeroExtend(~tmp[6:0]) + 1);
		4'd8 : tmp_differential_dc = (tmp[7] == 1) ? zeroExtend(tmp[7:0]) : (~zeroExtend(~tmp[7:0]) + 1);
		4'd9 : tmp_differential_dc = (tmp[8] == 1) ? zeroExtend(tmp[8:0]) : (~zeroExtend(~tmp[8:0]) + 1);
		4'd10: tmp_differential_dc = (tmp[9] == 1) ? zeroExtend(tmp[9:0]) : (~zeroExtend(~tmp[9:0]) + 1);
		4'd11: tmp_differential_dc = (tmp[10] == 1) ? zeroExtend(tmp[10:0]) : (~zeroExtend(~tmp[10:0]) + 1);
	  default: tmp_differential_dc = 0; 
     endcase
	 // Need to calculate DC coeff here and increase the dct_coeff_cnt
	 //dc_coeff = (tmp_differential_dc + scaled_dc_ref_value) * signExtend(dc_scaler);
	 //blkBuffer.write_d(tuple3(1,0,dc_coeff));
	 //acdcPredBuffer.upd(current_address_chroma,dc_coeff);
	 // commenting above as ac/dc prediction is done for intra blocks
	 // anyway and these values only come for them
	 // so dc prediction is done at one place in EXEC_ACDC_PREDICTION 
	 // state
	 blkBuffer.write_d(tuple3(1,0,tmp_differential_dc));
	 acdcPredBuffer.upd(current_address,Just(signExtend(tmp_differential_dc)));
	 $display("writing acdcPredBuffer addr = %d tmp_differential_dc = %h",current_address,tmp_differential_dc);
	 //dct_coeff_cnt <= 0;
	 dct_coeff_cnt <= 1;
	 byte_boundary <= byte_boundary + dct_dc_size_chroma[2:0];
	 if (sysState == START) 
	  begin 
	    sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
		byte_offset <= byte_offset +8 - zeroExtend(dct_dc_size_chroma);
	  end 
	else 
	  byte_offset <= byte_offset - zeroExtend(dct_dc_size_chroma);
    videoSt <= MB_BLK_STATE_10; 
  endrule

  rule mb_blk_state_10 (videoSt == MB_BLK_STATE_10);
    if (dct_dc_size_chroma > 8)
	  begin
	    if (byte_offset < 1) 
	      begin 
	        if (sysState == WAIT) 
	          videoSt  <= MB_BLK_STATE_11_0;
		    else 
              videoSt  <= MB_BLK_STATE_11; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8 ;
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 ;
		      end 
		    else 
		      byte_offset <= byte_offset ;
            videoSt  <= MB_BLK_STATE_11; 
          end 
	  end
	else
      videoSt  <= MB_BLK_STATE_12; 
  endrule

  rule wait_1_cycle79 ((videoSt == MB_BLK_STATE_11_0) && (vd_valid.wget == Just(1))) ; 
    videoSt <= MB_BLK_STATE_11; 
	$display("wait_1_cycle79 start code reg %h ",start_code_reg); 
  endrule

  rule mb_blk_state_11 (videoSt == MB_BLK_STATE_11);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	marker_bit <= tmp[0];
	byte_boundary <= byte_boundary + 1;
	 if (sysState == START) 
	  begin 
	    sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
		byte_offset <= byte_offset +8 - 1;
	  end 
	else 
	  byte_offset <= byte_offset - 1;
    videoSt <= MB_BLK_STATE_12;  // after code 1
  endrule

  rule mb_blk_state_12 (videoSt == MB_BLK_STATE_12);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
	//Bit#(12) dct_data = (tmp[0] == 1'b1) ? (~level + 1) : level;
	Bit#(12) dct_data ;
	Bit#(1)  sign ;
	Bit#(5)  tmp_byte_offset ;
	Bit#(12) inverse_quantised_dct_data ; 

    video_packet_header_detected <= False;
    start_code_detected <= False;
    if ((flc_type == NOTUSED) && (tmp[0] == 1))
	  begin
	    dct_data = ~level + 1;
		sign = 1;
	  end
	else
	  begin
	    dct_data  = level;
		sign = 0;
	  end
	  
	if (quant_type == 1)
	  inverse_quantised_dct_data = 
	         inverse_quant.getmethod1(sign,isIntra,dct_data,running_QP,weighting_matrix);
    else
	  inverse_quantised_dct_data = 
	         inverse_quant.getmethod2(sign,level,running_QP);

    $display("last %d run %d level %d pos %d sign %d addr %d",last,run,level,byte_offset,tmp[0],dct_coeff_cnt);
    if ((pattern_code) && (last == False))
	   begin
		 if (not_first_time)
		   begin
			 if ((acDCPredRequired) && 
			     (
				  (vertical_dir && 
			       (
				    (tmp_cbuff_addr == 0) || 
				    (tmp_cbuff_addr == 8) || 
				    (tmp_cbuff_addr == 16)|| 
				    (tmp_cbuff_addr == 24)|| 
				    (tmp_cbuff_addr == 32)|| 
				    (tmp_cbuff_addr == 40)|| 
				    (tmp_cbuff_addr == 48)|| 
				    (tmp_cbuff_addr == 56)
				   )
				  ) ||
				  (!vertical_dir && (tmp_cbuff_addr < 8))
				 ))
			    blkBuffer.write_d(tuple3(1,tmp_cbuff_addr,dct_data));
		     else
			   blkBuffer.write_d(tuple3(1,tmp_cbuff_addr,inverse_quantised_dct_data));
			 dct_coeff_cnt <= dct_coeff_cnt + 1;

			 if (flc_type == NOTUSED)
			   begin
			     tmp_byte_offset = byte_offset - 1;
			     byte_boundary <= byte_boundary + 1;
			   end
			 else
			   begin
			     tmp_byte_offset = byte_offset ;
			     byte_boundary <= byte_boundary ;
			   end

	         if (tmp_byte_offset < 13) 
	           begin 
	             if (sysState == WAIT) 
	               videoSt  <= MB_BLK_STATE_DCTVlc_0;
		         else 
                   videoSt  <= MB_BLK_STATE_DCTVlc; 
		         sysState <= START; 
		         vd_rd_reg <= 1'b1; 
		         byte_offset <= tmp_byte_offset +8  ;
	           end 
	         else
               begin 
	             if (sysState == START) 
		           begin 
			         sysState <= WAIT; 
			         vd_rd_reg <= 1'b0; 
		             byte_offset <= tmp_byte_offset +8 ;
		           end 
		         else 
		           byte_offset <= tmp_byte_offset ;
                 videoSt  <= MB_BLK_STATE_DCTVlc; 
               end 
		   end
		 else
		   begin
		     not_first_time <= True;
	         if (byte_offset < 13) 
	           begin 
	             if (sysState == WAIT) 
	               videoSt  <= MB_BLK_STATE_DCTVlc_0;
		         else 
                   videoSt  <= MB_BLK_STATE_DCTVlc; 
		         sysState <= START; 
		         vd_rd_reg <= 1'b1; 
		         byte_offset <= byte_offset +8 ;
	           end 
	         else
               begin 
	             if (sysState == START) 
		           begin 
			         sysState <= WAIT; 
			         vd_rd_reg <= 1'b0; 
		             byte_offset <= byte_offset +8 ;
		           end 
		         else 
		           byte_offset <= byte_offset ;
                 videoSt  <= MB_BLK_STATE_DCTVlc; 
               end 
		   end
	   end
	else if (pattern_code == False)
	  begin
		//if (acDCPredRequired && acDCPredDone == False)
		if (True && acDCPredDone == False)
		  begin
            videoSt  <= EXEC_ACDC_PREDICTION; 
			blkBuffer.read_d(tuple2(1,0));
		  end
		else 
		  begin
		    acDCPredDone <= False;
		    if (blk_cnt != 5)
		      begin
		        blk_cnt <= blk_cnt + 1;
				if (isIntra)
				  begin
				    pattern_code_d <= True;
				    pattern_code_2d <= True;
				  end
				else
				  begin
				    pattern_code_d <= pattern_code;
				    pattern_code_2d <= pattern_code_d;
				  end
			    vop_blk_num <= vop_blk_num + 1;
                videoSt <= MB_BLK_STATE;  // back to MB State
	            if (sysState == START) 
		          begin 
			        sysState <= WAIT; 
			        vd_rd_reg <= 1'b0; 
		            byte_offset <= byte_offset +8 ;
		          end 
		        else 
		          byte_offset <= byte_offset ;
		      end
		    else
		      begin
		        blk_cnt <= 0;
				if (isIntra)
				  begin
				    pattern_code_d <= True;
				    pattern_code_2d <= True;
				  end
				else
				  begin
				    pattern_code_d <= pattern_code;
				    pattern_code_2d <= pattern_code_d;
				  end
			    vop_blk_num <= 0;
			    if (zeroExtend(mb_num_x) == (mb_width -1))
			      begin
			        mb_num_x <= 0;
			        mb_num_y <= mb_num_y + 1;
			      end
			    else if ((zeroExtend(mb_num_y) == (mb_height -1)) && (zeroExtend(mb_num_x) == (mb_width -1)))
			      begin
			        mb_num_x <= 0;
			        mb_num_y <= 0;
			      end
			    else
			      mb_num_x <= mb_num_x + 1;
			    //mb_num_y_d <= mb_num_y;
			    if (zeroExtend(vop_mb_num_x) == (mb_width-1))
			      begin
			        vop_mb_num_x <= 0;
			        vop_mb_num_y <= vop_mb_num_y + 1;
			      end
			    else
			      vop_mb_num_x <= vop_mb_num_x + 1;
	            if (sysState == START) 
		          begin 
			        sysState <= WAIT; 
			        vd_rd_reg <= 1'b0; 
		            byte_offset <= byte_offset +8 ;
		          end 
		        else 
		          byte_offset <= byte_offset ;
                videoSt <= CHECK_RESYNC_MARKER0;
		      end
		  end
	  end
	else
	  begin
		//if (acDCPredRequired && acDCPredDone == False)
		if (True && acDCPredDone == False)
		  begin
             // if last data needs to be predicted then
			 // write the dct value in buffer
			 // e.w write the inverse quantised value
			 if (acDCPredRequired && 
			      (
				   (vertical_dir && 
			       ((tmp_cbuff_addr == 0) || 
				    (tmp_cbuff_addr == 8) || 
				    (tmp_cbuff_addr == 16)|| 
				    (tmp_cbuff_addr == 24)|| 
				    (tmp_cbuff_addr == 32)|| 
				    (tmp_cbuff_addr == 40)|| 
				    (tmp_cbuff_addr == 48)|| 
				    (tmp_cbuff_addr == 56))
				   ) ||
				  (!vertical_dir && (tmp_cbuff_addr < 8))
				 )
				)
			    blkBuffer.write_d(tuple3(1,tmp_cbuff_addr,dct_data));
		     else
			   blkBuffer.write_d(tuple3(1,tmp_cbuff_addr,inverse_quantised_dct_data));
			dct_coeff_cnt <= dct_coeff_cnt + 1;
            videoSt  <= EXEC_ACDC_PREDICTION; 
			blkBuffer.read_d(tuple2(1,0));
		    // last sign bit is read need to make sure its been used or not
			if (flc_type == NOTUSED)
			   begin
			     tmp_byte_offset = byte_offset - 1;
				 byte_boundary <= byte_boundary + 1;
			   end
			else
			   begin
			     tmp_byte_offset = byte_offset ;
				 byte_boundary <= byte_boundary ;
			   end

	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= tmp_byte_offset +8 ;
		      end 
		    else 
		      byte_offset <= tmp_byte_offset ;
		  end
		//else if (acDCPredRequired == False || acDCPredDone )
		else if (acDCPredDone )
		  begin
	        not_first_time <= False;
			acDCPredDone <= False;
			// only write the last data into buffer if AC/DC pred is not required
			// e.w it has been taken care of when not_first_time is true
			//if (acDCPredRequired == False)
			//blkBuffer.write_d(tuple3(1,tmp_cbuff_addr,inverse_quantised_dct_data));
		    if (blk_cnt != 5)
		      begin
		        blk_cnt <= blk_cnt + 1;
				if (isIntra)
				  begin
				    pattern_code_d <= True;
				    pattern_code_2d <= True;
				  end
				else
				  begin
				    pattern_code_d <= pattern_code;
				    pattern_code_2d <= pattern_code_d;
				  end
			    vop_blk_num <= vop_blk_num + 1;
                videoSt <= MB_BLK_STATE;  // back to MB State
				/*
				if (acDCPredRequired == False)
				   begin
		             // last sign bit is read need to make sure its been used or not
			         if (flc_type == NOTUSED)
					   begin
			             tmp_byte_offset = byte_offset - 1;
				         byte_boundary <= byte_boundary + 1;
					   end
			         else
					   begin
			             tmp_byte_offset = byte_offset ;
				         byte_boundary <= byte_boundary ;
					   end

	                 if (sysState == START) 
		               begin 
			             sysState <= WAIT; 
			             vd_rd_reg <= 1'b0; 
		                 byte_offset <= tmp_byte_offset +8 ;
		               end 
		             else 
		               byte_offset <= tmp_byte_offset ;
				   end
				   */
		      end
		    else
		      begin
		        blk_cnt <= 0;
				if (isIntra)
				  begin
				    pattern_code_d <= True;
				    pattern_code_2d <= True;
				  end
				else
				  begin
				    pattern_code_d <= pattern_code;
				    pattern_code_2d <= pattern_code_d;
				  end
			    vop_blk_num <= 0;
			    if (zeroExtend(mb_num_x) == (mb_width -1))
			      begin
			        mb_num_x <= 0;
			        mb_num_y <= mb_num_y + 1;
			      end
			    else if ((zeroExtend(mb_num_y) == (mb_height -1)) && (zeroExtend(mb_num_x) == (mb_width -1)))
			      begin
			        mb_num_x <= 0;
			        mb_num_y <= 0;
			      end
			    else
			        mb_num_x <= mb_num_x + 1;
			    //mb_num_y_d <= mb_num_y;
    
			    if (zeroExtend(vop_mb_num_x) == (mb_width-1))
			      begin
			        vop_mb_num_x <= 0;
			        vop_mb_num_y <= vop_mb_num_y + 1;
			      end
			    else
			      vop_mb_num_x <= vop_mb_num_x + 1;
				  /*
				if (acDCPredRequired == False)
				   begin
		             // last sign bit is read need to make sure its been used or not
			         if (flc_type == NOTUSED)
					   begin
			             tmp_byte_offset = byte_offset - 1;
				         byte_boundary <= byte_boundary + 1;
					   end
			         else
					   begin
			             tmp_byte_offset = byte_offset ;
				         byte_boundary <= byte_boundary ;
					   end

	                 if (sysState == WAIT) 
		               begin 
			             sysState <= START; 
			             vd_rd_reg <= 1'b1; 
		                 byte_offset <= tmp_byte_offset ;
		               end 
		             else 
		               byte_offset <= tmp_byte_offset +8 ;
				   end
				else
				  begin
		            sysState <= START; 
		            vd_rd_reg <= 1'b1; 
				  end
				*/
		        sysState <= START; 
		        vd_rd_reg <= 1'b1; 
                videoSt <= CHECK_RESYNC_MARKER0;
		      end
		  end
	  end

  endrule

  rule wait_1_cycle80 ((videoSt == MB_BLK_STATE_DCTVlc_0) && (vd_valid.wget == Just(1))) ; 
    if (byte_offset < 13)  // max VLC is of length 12 + 1 for sign bit
	  begin
	    //byte_offset <= byte_offset + 8;
        videoSt <= MB_BLK_STATE_DCTVlc_0_0; 
	  end
	else
       videoSt <= MB_BLK_STATE_DCTVlc; 
	$display("wait_1_cycle79 start code reg %h ",start_code_reg); 
  endrule

  rule wait_1_cycle80_1 ((videoSt == MB_BLK_STATE_DCTVlc_0_0) && (vd_valid.wget == Just(1))) ; 
     byte_offset <= byte_offset + 8;
     videoSt <= MB_BLK_STATE_DCTVlc; 
     $display("wait_1_cycle80_1 start code reg %h ",start_code_reg); 
  endrule

  rule mb_blk_state_dctvlc (videoSt == MB_BLK_STATE_DCTVlc);
     Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,9);
     Bit#(5)  tmp_byte_offset = 0;
     $display("mb_blk_state_dctvlc tmp = %h",tmp[8:0]);
     if (isIntra)
	begin
           if (tmp[8] == 1)
	      begin
		 byte_boundary <= byte_boundary + 1;
	         tmp_byte_offset = byte_offset - 1;
                 videoSt <= DecodeVLCIntraTable1; 
	      end
           else if (tmp[7] == 1)
	      begin
		 byte_boundary <= byte_boundary + 2;
	         tmp_byte_offset = byte_offset - 2;
                 videoSt <= DecodeVLCIntraTable2; 
	      end
           else if (tmp[6] == 1)
	      begin
		 byte_boundary <= byte_boundary + 3;
	         tmp_byte_offset = byte_offset - 3;
                 videoSt <= DecodeVLCIntraTable3; 
	      end
           else if (tmp[5] == 1)
	      begin
		 byte_boundary <= byte_boundary + 4;
	         tmp_byte_offset = byte_offset - 4;
                 videoSt <= DecodeVLCIntraTable4; 
	      end
           else if (tmp[4] == 1)
	      begin
		 byte_boundary <= byte_boundary + 5;
	         tmp_byte_offset = byte_offset - 5;
                 videoSt <= DecodeVLCIntraTable5; 
	      end
           else if (tmp[3:2] == 2'b10)
	      begin
		 byte_boundary <= byte_boundary + 7;
	         tmp_byte_offset = byte_offset - 7;
                 videoSt <= DecodeVLCIntraTable6; 
	      end
           else if (tmp[3:2] == 2'b11)
	      begin
		 byte_boundary <= byte_boundary + 7;
	         tmp_byte_offset = byte_offset - 7;
                 videoSt <= Fixed_length_code; 
	      end
           else if (tmp[3:2] == 2'b01)
	      begin
		 byte_boundary <= byte_boundary + 7;
	         tmp_byte_offset = byte_offset - 7;
                 videoSt <= DecodeVLCIntraTable7; 
	      end
           else if (tmp[1] == 1)
	      begin
		 byte_boundary <= byte_boundary ;
	         tmp_byte_offset = byte_offset - 8;
                 videoSt <= DecodeVLCIntraTable8; 
	      end
           else if (tmp[0] == 1)
	      begin
		 byte_boundary <= byte_boundary + 1;
	         tmp_byte_offset = byte_offset - 9;
                 videoSt <= DecodeVLCIntraTable9; 
	      end
           else
	      $display("Error Invalid VLC coding");
	   if (sysState == START)
	      begin
	         sysState <= WAIT; 
	         vd_rd_reg <= 1'b0; 
		 byte_offset <= tmp_byte_offset + 8;
	      end
	   else
	      byte_offset <= tmp_byte_offset ;
	end
     else if ((mbtype == 0) || (mbtype == 1))
	begin
           if (tmp[8] == 1)
	      begin
		 byte_boundary <= byte_boundary + 1;
	         tmp_byte_offset = byte_offset - 1;
                 videoSt <= DecodeVLCInterTable1; 
	      end
           else if (tmp[7] == 1)
	      begin
		 byte_boundary <= byte_boundary + 2;
	         tmp_byte_offset = byte_offset - 2;
                 videoSt <= DecodeVLCInterTable2; 
	      end
           else if (tmp[6] == 1)
	      begin
		 byte_boundary <= byte_boundary + 3;
	         tmp_byte_offset = byte_offset - 3;
                 videoSt <= DecodeVLCInterTable3; 
	      end
           else if (tmp[5] == 1)
	      begin
		 byte_boundary <= byte_boundary + 4;
	         tmp_byte_offset = byte_offset - 4;
                 videoSt <= DecodeVLCInterTable4; 
	      end
           else if (tmp[4] == 1)
	      begin
		 byte_boundary <= byte_boundary + 5;
	         tmp_byte_offset = byte_offset - 5;
                 videoSt <= DecodeVLCInterTable5; 
	      end
           else if (tmp[3:2] == 2'b10)
	      begin
		 byte_boundary <= byte_boundary + 7;
	         tmp_byte_offset = byte_offset - 7;
                 videoSt <= DecodeVLCInterTable6; 
	      end
           else if (tmp[3:2] == 2'b11)
	      begin
		 byte_boundary <= byte_boundary + 7;
	         tmp_byte_offset = byte_offset - 7;
                 videoSt <= Fixed_length_code; 
	      end
           else if (tmp[3:2] == 2'b01)
	      begin
		 byte_boundary <= byte_boundary + 7;
	         tmp_byte_offset = byte_offset - 7;
                 videoSt <= DecodeVLCInterTable7; 
	      end
           else if (tmp[1] == 1)
	      begin
		 byte_boundary <= byte_boundary ;
	         tmp_byte_offset = byte_offset - 8;
                 videoSt <= DecodeVLCInterTable8; 
	      end
           else if (tmp[0] == 1)
	      begin
		 byte_boundary <= byte_boundary + 1;
	         tmp_byte_offset = byte_offset - 9;
                 videoSt <= DecodeVLCInterTable9; 
	      end
           else
	      $display("Error Invalid VLC coding");
	   if (sysState == START)
	      begin
	         sysState <= WAIT; 
	         vd_rd_reg <= 1'b0; 
	         byte_offset <= tmp_byte_offset +8;
	      end
	   else
	      byte_offset <= tmp_byte_offset ;
	end
     else 
	begin
	   $display("Error Invalid mbtype = ", mbtype);
	end
  endrule

  rule fixed_length_code_type (videoSt == Fixed_length_code);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,2);
	Bit#(5)  tmp_byte_offset = 0;
	$display("fixed_length_code_type tmp = %h",tmp[1:0]);
	if (short_video_header) // type 4 FLC
	  begin
		flc_type <= TYPE4;
	    if (byte_offset < 7) 
	      begin 
	        if (sysState == WAIT) 
	          videoSt  <= MB_BLK_STATE_FLC_Type3_0;
		    else 
              videoSt  <= MB_BLK_STATE_FLC_Type3; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset +8 ;
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset +8 ;
		      end 
		    else 
		      byte_offset <= byte_offset ;
            videoSt  <= MB_BLK_STATE_FLC_Type3; 
          end 
	  end
	else
	  begin
	    if ((tmp[1] == 0) || (tmp[1:0] == 2'b10))
	      begin
	        if (tmp[1] == 0)  // type 1 FLC
	          begin
			    byte_boundary <= byte_boundary + 1;
	            tmp_byte_offset = byte_offset - 1;
		        flc_type   <= TYPE1;
	          end
	        else              // type 2 FLC
	          begin
			    byte_boundary <= byte_boundary + 2;
	            tmp_byte_offset = byte_offset - 2;
		        flc_type   <= TYPE2;
	          end
	        if (tmp_byte_offset < 13) 
	           begin 
	             if (sysState == WAIT) 
	               videoSt  <= MB_BLK_STATE_DCTVlc_0;
		         else 
                   videoSt  <= MB_BLK_STATE_DCTVlc; 
		         sysState <= START; 
		         vd_rd_reg <= 1'b1; 
		         byte_offset <= tmp_byte_offset +8 ;
	           end 
	        else
               begin 
	             if (sysState == START) 
		           begin 
			         sysState <= WAIT; 
			         vd_rd_reg <= 1'b0; 
		             byte_offset <= tmp_byte_offset +8 ;
		           end 
		         else 
		           byte_offset <= tmp_byte_offset ;
                 videoSt  <= MB_BLK_STATE_DCTVlc; 
               end 
	      end
		else                        // type 3 FLC
	      begin
			byte_boundary <= byte_boundary + 2;
	        tmp_byte_offset = byte_offset - 2;
		    flc_type   <= TYPE3;
	        if (byte_offset < 10) 
	           begin 
	             if (sysState == WAIT) 
	               videoSt  <= MB_BLK_STATE_FLC_Type3_0;
		         else 
                   videoSt  <= MB_BLK_STATE_FLC_Type3; 
		         sysState <= START; 
		         vd_rd_reg <= 1'b1; 
		         byte_offset <= tmp_byte_offset +8 ;
	           end 
	        else
               begin 
	             if (sysState == START) 
		           begin 
			         sysState <= WAIT; 
			         vd_rd_reg <= 1'b0; 
		             byte_offset <= tmp_byte_offset +8 ;
		           end 
		         else 
		           byte_offset <= tmp_byte_offset ;
                 videoSt  <= MB_BLK_STATE_FLC_Type3; 
	           end
	      end
	  end
  endrule

  rule fixed_length_code_type3_0 (videoSt == MB_BLK_STATE_FLC_Type3_0);
    videoSt <= MB_BLK_STATE_FLC_Type3; 
	$display("wait_1_cycleFLC_type3 start code reg %h ",start_code_reg); 
  endrule

  rule fixed_length_code_type3 (videoSt == MB_BLK_STATE_FLC_Type3);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	Bit#(5)  tmp_byte_offset = 0;
	if (tmp[7] == 1)
	  last <= True;
	else
	  last <= False;
	run <= tmp[6:1];
    //dct_coeff_cnt <= dct_coeff_cnt +  tmp[6:1] + 1;
    dct_coeff_cnt <= dct_coeff_cnt +  tmp[6:1] ;
	if (flc_type == TYPE3)
	  begin
	    marker_bit <= tmp[0];
		tmp_byte_offset = byte_offset - 8;
	    byte_boundary <= byte_boundary ;
	  end
	else
	  begin
	    byte_boundary <= byte_boundary + 7;
	    tmp_byte_offset = byte_offset - 7;
	  end
	if (tmp_byte_offset < 8) 
	  begin 
	    if (sysState == WAIT) 
	      videoSt  <= MB_BLK_STATE_FLC_Type3_1_0;
		else 
          videoSt  <= MB_BLK_STATE_FLC_Type3_1; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
		byte_offset <= tmp_byte_offset + 8;
	  end 
	else
      begin 
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= tmp_byte_offset + 8;
		  end 
		else 
		  byte_offset <= tmp_byte_offset ;
        videoSt  <= MB_BLK_STATE_FLC_Type3_1; 
      end 
  endrule

  rule fixed_length_code_type3_1_0 (videoSt == MB_BLK_STATE_FLC_Type3_1_0);
    videoSt <= MB_BLK_STATE_FLC_Type3_1; 
	$display("wait_1_cycleFLC_type3_1 start code reg %h ",start_code_reg); 
  endrule

  rule fixed_length_code_type3_1 (videoSt == MB_BLK_STATE_FLC_Type3_1);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
	level <= zeroExtend(tmp[7:0]);
	if (flc_type == TYPE3)
	  begin
	    if (byte_offset < 13) 
	      begin 
	        if (sysState == WAIT) 
	          videoSt  <= MB_BLK_STATE_FLC_Type3_2_0;
		    else 
              videoSt  <= MB_BLK_STATE_FLC_Type3_2; 
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
		    byte_offset <= byte_offset ;
	      end 
	    else
          begin 
	        if (sysState == START) 
		      begin 
			    sysState <= WAIT; 
			    vd_rd_reg <= 1'b0; 
		        byte_offset <= byte_offset ;
		      end 
		    else 
		      byte_offset <= byte_offset - 8;
            videoSt  <= MB_BLK_STATE_FLC_Type3_2; 
          end 
	  end
	else
	  begin
	    if (sysState == START) 
		  begin 
			sysState <= WAIT; 
			vd_rd_reg <= 1'b0; 
		    byte_offset <= byte_offset ;
		  end 
		else 
		  byte_offset <= byte_offset - 8;
        videoSt  <= MB_BLK_STATE_12; 
		//flc_type <= NOTUSED;
	  end
  endrule

  rule fixed_length_code_type3_2_0 (videoSt == MB_BLK_STATE_FLC_Type3_2_0);
    videoSt <= MB_BLK_STATE_FLC_Type3_2; 
	$display("wait_1_cycleFLC_type3_2 start code reg %h ",start_code_reg); 
  endrule

  rule fixed_length_code_type3_2 (videoSt == MB_BLK_STATE_FLC_Type3_2);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,5);
	level <= {level[7:0],tmp[4:1]};
	marker_bit <= tmp[0];
	if (sysState == START) 
	  begin 
		sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
	    byte_offset <= byte_offset +8 -5;
	  end 
	else 
	  byte_offset <= byte_offset - 5;
	byte_boundary <= byte_boundary + 5;
    videoSt  <= MB_BLK_STATE_12; 
	//flc_type <= NOTUSED;
  endrule

  rule decodevlcintratable1 (videoSt == DecodeVLCIntraTable1);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,3);
	Bit#(7)  decodedVLC = vlc_intra_table_1.sub(tmp[2:0]);
	Bool tmp_last;
	Bit#(6) tmp_run;
	Bit#(12) tmp_level;
	tmp_last = (decodedVLC[3]== 1);
	tmp_run =  zeroExtend(decodedVLC[2]);
	tmp_level = zeroExtend(decodedVLC[1:0]);

    if (flc_type == TYPE1)
	  tmp_level = tmp_level + flc.lmax(tmp_last,tmp_run,isIntra);
	else
	  tmp_level = tmp_level ;
	if (flc_type == TYPE2)
	   tmp_run = tmp_run + flc.rmax(tmp_last,tmp_level,isIntra);
	else
	   tmp_run = tmp_run ;
	flc_type <= NOTUSED;
	last <= tmp_last;
	run <= tmp_run;
	level <= tmp_level;
	byte_boundary <= byte_boundary + zeroExtend(decodedVLC[5:4]);
	byte_offset <= byte_offset - zeroExtend(decodedVLC[5:4]);
    //dct_coeff_cnt <= dct_coeff_cnt +  tmp_run + 1;
    dct_coeff_cnt <= dct_coeff_cnt +  tmp_run ;
    videoSt <= MB_BLK_STATE_12; 
  endrule

  rule decodevlcintratable2 (videoSt == DecodeVLCIntraTable2);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,4);
	Bit#(12)  decodedVLC = vlc_intra_table_2.sub(tmp[3:0]);
	Bool tmp_last;
	Bit#(6) tmp_run;
	Bit#(12) tmp_level;
	tmp_last = (decodedVLC[7] == 1);
	tmp_run =  zeroExtend(decodedVLC[6:4]);
	tmp_level = zeroExtend(decodedVLC[3:0]);
    if (flc_type == TYPE1)
	  tmp_level = tmp_level + flc.lmax(tmp_last,tmp_run,isIntra);
	else
	  tmp_level = tmp_level ;
	if (flc_type == TYPE2)
	   tmp_run = tmp_run + flc.rmax(tmp_last,tmp_level,isIntra);
	else
	   tmp_run = tmp_run ;
	flc_type <= NOTUSED;
	last <= tmp_last;
	run <= tmp_run;
	level <= tmp_level;
	byte_boundary <= byte_boundary + decodedVLC[10:8];
	byte_offset <= byte_offset - zeroExtend(decodedVLC[10:8]) ;
    //dct_coeff_cnt <= dct_coeff_cnt +  tmp_run + 1;
    dct_coeff_cnt <= dct_coeff_cnt +  tmp_run ;
    videoSt <= MB_BLK_STATE_12; 
  endrule

  rule decodevlcintratable3 (videoSt == DecodeVLCIntraTable3);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,4);
	Bit#(12)  decodedVLC = vlc_intra_table_3.sub(tmp[3:0]);
	Bool tmp_last;
	Bit#(6) tmp_run;
	Bit#(12) tmp_level;
	tmp_last = (decodedVLC[7] == 1);
	tmp_run =  zeroExtend(decodedVLC[6:4]);
	tmp_level = zeroExtend(decodedVLC[3:0]);
    if (flc_type == TYPE1)
	  tmp_level = tmp_level + flc.lmax(tmp_last,tmp_run,isIntra);
	else
	  tmp_level = tmp_level ;
	if (flc_type == TYPE2)
	   tmp_run = tmp_run + flc.rmax(tmp_last,tmp_level,isIntra);
	else
	   tmp_run = tmp_run ;
	flc_type <= NOTUSED;
	last <= tmp_last;
	run <= tmp_run;
	level <= tmp_level;
	byte_boundary <= byte_boundary + decodedVLC[10:8];
	byte_offset <= byte_offset - zeroExtend(decodedVLC[10:8]) ;
    //dct_coeff_cnt <= dct_coeff_cnt +  tmp_run + 1;
    dct_coeff_cnt <= dct_coeff_cnt +  tmp_run ;
    videoSt <= MB_BLK_STATE_12; 
  endrule

  rule decodevlcintratable4 (videoSt == DecodeVLCIntraTable4);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,5);
	Bit#(14)  decodedVLC = vlc_intra_table_4.sub(tmp[4:0]);
	Bool tmp_last;
	Bit#(6) tmp_run;
	Bit#(12) tmp_level;
	tmp_last = (decodedVLC[9] == 1);
	tmp_run =  zeroExtend(decodedVLC[8:5]);
	tmp_level = zeroExtend(decodedVLC[4:0]);
    if (flc_type == TYPE1)
	  tmp_level = tmp_level + flc.lmax(tmp_last,tmp_run,isIntra);
	else
	  tmp_level = tmp_level ;
	if (flc_type == TYPE2)
	   tmp_run = tmp_run + flc.rmax(tmp_last,tmp_level,isIntra);
	else
	   tmp_run = tmp_run ;
	flc_type <= NOTUSED;
	last <= tmp_last;
	run <= tmp_run;
	level <= tmp_level;
	byte_boundary <= byte_boundary + decodedVLC[12:10];
	byte_offset <= byte_offset - zeroExtend(decodedVLC[12:10]) ;
    //dct_coeff_cnt <= dct_coeff_cnt +  tmp_run + 1;
    dct_coeff_cnt <= dct_coeff_cnt +  tmp_run ;
    videoSt <= MB_BLK_STATE_12; 
  endrule

  rule decodevlcintratable5 (videoSt == DecodeVLCIntraTable5);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,5);
	Bit#(14)  decodedVLC = vlc_intra_table_5.sub(tmp[4:0]);
	Bool tmp_last;
	Bit#(6) tmp_run;
	Bit#(12) tmp_level;
	tmp_last = (decodedVLC[9] == 1);
	tmp_run =  zeroExtend(decodedVLC[8:5]);
	tmp_level = zeroExtend(decodedVLC[4:0]);
    if (flc_type == TYPE1)
	  tmp_level = tmp_level + flc.lmax(tmp_last,tmp_run,isIntra);
	else
	  tmp_level = tmp_level ;
	if (flc_type == TYPE2)
	   tmp_run = tmp_run + flc.rmax(tmp_last,tmp_level,isIntra);
	else
	   tmp_run = tmp_run ;
	flc_type <= NOTUSED;
	last <= tmp_last;
	run <= tmp_run;
	level <= tmp_level;
	byte_boundary <= byte_boundary + decodedVLC[12:10];
	byte_offset <= byte_offset - zeroExtend(decodedVLC[12:10]) ;
    //dct_coeff_cnt <= dct_coeff_cnt +  tmp_run + 1;
    dct_coeff_cnt <= dct_coeff_cnt +  tmp_run ;
    videoSt <= MB_BLK_STATE_12; 
  endrule

  rule decodevlcintratable6 (videoSt == DecodeVLCIntraTable6);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,5);
	Bit#(15)  decodedVLC = vlc_intra_table_6.sub(tmp[4:0]);
	Bool tmp_last;
	Bit#(6) tmp_run;
	Bit#(12) tmp_level;
	tmp_last = (decodedVLC[10] == 1);
	tmp_run =  zeroExtend(decodedVLC[9:5]);
	tmp_level = zeroExtend(decodedVLC[4:0]);
    if (flc_type == TYPE1)
	  tmp_level = tmp_level + flc.lmax(tmp_last,tmp_run,isIntra);
	else
	  tmp_level = tmp_level ;
	if (flc_type == TYPE2)
	   tmp_run = tmp_run + flc.rmax(tmp_last,tmp_level,isIntra);
	else
	   tmp_run = tmp_run ;
	flc_type <= NOTUSED;
	last <= tmp_last;
	run <= tmp_run;
	level <= tmp_level;
	byte_boundary <= byte_boundary + decodedVLC[13:11];
	byte_offset <= byte_offset - zeroExtend(decodedVLC[13:11]) ;
    //dct_coeff_cnt <= dct_coeff_cnt +  tmp_run + 1;
    dct_coeff_cnt <= dct_coeff_cnt +  tmp_run ;
    videoSt <= MB_BLK_STATE_12; 
  endrule

  rule decodevlcintratable7 (videoSt == DecodeVLCIntraTable7);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,3);
	Bit#(13)  decodedVLC = vlc_intra_table_7.sub(tmp[2:0]);
	Bool tmp_last;
	Bit#(6) tmp_run;
	Bit#(12) tmp_level;
	tmp_last = (decodedVLC[9] == 1);
	tmp_run =  zeroExtend(decodedVLC[8:5]);
	tmp_level = zeroExtend(decodedVLC[4:0]);
    if (flc_type == TYPE1)
	  tmp_level = tmp_level + flc.lmax(tmp_last,tmp_run,isIntra);
	else
	  tmp_level = tmp_level ;
	if (flc_type == TYPE2)
	   tmp_run = tmp_run + flc.rmax(tmp_last,tmp_level,isIntra);
	else
	   tmp_run = tmp_run ;
	flc_type <= NOTUSED;
	last <= tmp_last;
	run <= tmp_run;
	level <= tmp_level;
	byte_boundary <= byte_boundary + zeroExtend(decodedVLC[11:10]);
	byte_offset <= byte_offset - zeroExtend(decodedVLC[11:10]) ;
    //dct_coeff_cnt <= dct_coeff_cnt +  tmp_run + 1;
    dct_coeff_cnt <= dct_coeff_cnt +  tmp_run ;
    videoSt <= MB_BLK_STATE_12; 
  endrule

  rule decodevlcintratable8 (videoSt == DecodeVLCIntraTable8);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,2);
	Bit#(12)  decodedVLC = vlc_intra_table_8.sub(tmp[1:0]);
	Bool tmp_last;
	Bit#(6) tmp_run;
	Bit#(12) tmp_level;
	tmp_last = (decodedVLC[8] == 1);
	tmp_run =  zeroExtend(decodedVLC[7:4]);
	tmp_level = zeroExtend(decodedVLC[3:0]);
    if (flc_type == TYPE1)
	  tmp_level = tmp_level + flc.lmax(tmp_last,tmp_run,isIntra);
	else
	  tmp_level = tmp_level ;
	if (flc_type == TYPE2)
	   tmp_run = tmp_run + flc.rmax(tmp_last,tmp_level,isIntra);
	else
	   tmp_run = tmp_run ;
	flc_type <= NOTUSED;
	last <= tmp_last;
	run <= tmp_run;
	level <= tmp_level;
	byte_boundary <= byte_boundary + zeroExtend(decodedVLC[10:9]);
	byte_offset <= byte_offset - zeroExtend(decodedVLC[10:9]) ;
    //dct_coeff_cnt <= dct_coeff_cnt +  tmp_run + 1;
    dct_coeff_cnt <= dct_coeff_cnt +  tmp_run ;
    videoSt <= MB_BLK_STATE_12; 
  endrule

  rule decodevlcintratable9 (videoSt == DecodeVLCIntraTable9);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,2);
	Bit#(13)  decodedVLC = vlc_intra_table_9.sub(tmp[1:0]);
	Bool tmp_last;
	Bit#(6) tmp_run;
	Bit#(12) tmp_level;
	tmp_last = (decodedVLC[9] == 1);
	tmp_run =  zeroExtend(decodedVLC[8:5]);
	tmp_level = zeroExtend(decodedVLC[4:0]);
    if (flc_type == TYPE1)
	  tmp_level = tmp_level + flc.lmax(tmp_last,tmp_run,isIntra);
	else
	  tmp_level = tmp_level ;
	if (flc_type == TYPE2)
	   tmp_run = tmp_run + flc.rmax(tmp_last,tmp_level,isIntra);
	else
	   tmp_run = tmp_run ;
	flc_type <= NOTUSED;
	last <= tmp_last;
	run <= tmp_run;
	level <= tmp_level;
	byte_boundary <= byte_boundary + zeroExtend(decodedVLC[11:10]);
	byte_offset <= byte_offset - zeroExtend(decodedVLC[11:10]) ;
    //dct_coeff_cnt <= dct_coeff_cnt +  tmp_run + 1;
    dct_coeff_cnt <= dct_coeff_cnt +  tmp_run ;
    videoSt <= MB_BLK_STATE_12; 
  endrule

  rule decodevlcintertable1 (videoSt == DecodeVLCInterTable1);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,3);
	Bit#(7)  decodedVLC = vlc_inter_table_1.sub(tmp[2:0]);
	Bool tmp_last;
	Bit#(6) tmp_run;
	Bit#(12) tmp_level;
	tmp_last = (decodedVLC[4] == 1);
	tmp_run =  zeroExtend(decodedVLC[3:2]);
	tmp_level = zeroExtend(decodedVLC[1:0]);
    if (flc_type == TYPE1)
	  tmp_level = tmp_level + flc.lmax(tmp_last,tmp_run,isIntra);
	else
	  tmp_level = tmp_level ;
	if (flc_type == TYPE2)
	   tmp_run = tmp_run + flc.rmax(tmp_last,tmp_level,isIntra);
	else
	   tmp_run = tmp_run ;
	flc_type <= NOTUSED;
	last <= tmp_last;
	run <= tmp_run;
	level <= tmp_level;
	byte_boundary <= byte_boundary + zeroExtend(decodedVLC[6:5]);
	byte_offset <= byte_offset - zeroExtend(decodedVLC[6:5]);
    //dct_coeff_cnt <= dct_coeff_cnt +  tmp_run + 1;
    dct_coeff_cnt <= dct_coeff_cnt +  tmp_run ;
    videoSt <= MB_BLK_STATE_12; 
  endrule

  rule decodevlcintertable2 (videoSt == DecodeVLCInterTable2);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,4);
	Bit#(10)  decodedVLC = vlc_inter_table_2.sub(tmp[3:0]);
	Bool tmp_last;
	Bit#(6) tmp_run;
	Bit#(12) tmp_level;
	tmp_last = (decodedVLC[6] == 1);
	tmp_run =  zeroExtend(decodedVLC[5:2]);
	tmp_level = zeroExtend(decodedVLC[1:0]);
    if (flc_type == TYPE1)
	  tmp_level = tmp_level + flc.lmax(tmp_last,tmp_run,isIntra);
	else
	  tmp_level = tmp_level ;
	if (flc_type == TYPE2)
	   tmp_run = tmp_run + flc.rmax(tmp_last,tmp_level,isIntra);
	else
	   tmp_run = tmp_run ;
	flc_type <= NOTUSED;
	last <= tmp_last;
	run <= tmp_run;
	level <= tmp_level;
	byte_boundary <= byte_boundary + decodedVLC[9:7];
	byte_offset <= byte_offset - zeroExtend(decodedVLC[9:7]) ;
    //dct_coeff_cnt <= dct_coeff_cnt +  tmp_run + 1;
    dct_coeff_cnt <= dct_coeff_cnt +  tmp_run ;
    videoSt <= MB_BLK_STATE_12; 
  endrule

  rule decodevlcintertable3 (videoSt == DecodeVLCInterTable3);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,4);
	Bit#(11)  decodedVLC = vlc_inter_table_3.sub(tmp[3:0]);
	Bool tmp_last;
	Bit#(6) tmp_run;
	Bit#(12) tmp_level;
	tmp_last = (decodedVLC[7] == 1);
	tmp_run =  zeroExtend(decodedVLC[6:3]);
	tmp_level = zeroExtend(decodedVLC[2:0]);
    if (flc_type == TYPE1)
	  tmp_level = tmp_level + flc.lmax(tmp_last,tmp_run,isIntra);
	else
	  tmp_level = tmp_level ;
	if (flc_type == TYPE2)
	   tmp_run = tmp_run + flc.rmax(tmp_last,tmp_level,isIntra);
	else
	   tmp_run = tmp_run ;
	flc_type <= NOTUSED;
	last <= tmp_last;
	run <= tmp_run;
	level <= tmp_level;
	byte_boundary <= byte_boundary + decodedVLC[10:8];
	byte_offset <= byte_offset - zeroExtend(decodedVLC[10:8]) ;
    //dct_coeff_cnt <= dct_coeff_cnt +  tmp_run + 1;
    dct_coeff_cnt <= dct_coeff_cnt +  tmp_run ;
    videoSt <= MB_BLK_STATE_12; 
  endrule

  rule decodevlcintertable4 (videoSt == DecodeVLCInterTable4);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,5);
	Bit#(12)  decodedVLC = vlc_inter_table_4.sub(tmp[4:0]);
	Bool tmp_last;
	Bit#(6) tmp_run;
	Bit#(12) tmp_level;
	tmp_last = (decodedVLC[8] == 1);
	tmp_run =  zeroExtend(decodedVLC[7:3]);
	tmp_level = zeroExtend(decodedVLC[2:0]);
    if (flc_type == TYPE1)
	  tmp_level = tmp_level + flc.lmax(tmp_last,tmp_run,isIntra);
	else
	  tmp_level = tmp_level ;
	if (flc_type == TYPE2)
	   tmp_run = tmp_run + flc.rmax(tmp_last,tmp_level,isIntra);
	else
	   tmp_run = tmp_run ;
	flc_type <= NOTUSED;
	last <= tmp_last;
	run <= tmp_run;
	level <= tmp_level;
	byte_boundary <= byte_boundary + decodedVLC[11:9];
	byte_offset <= byte_offset - zeroExtend(decodedVLC[11:9]) ;
    //dct_coeff_cnt <= dct_coeff_cnt +  tmp_run + 1;
    dct_coeff_cnt <= dct_coeff_cnt +  tmp_run ;
    videoSt <= MB_BLK_STATE_12; 
  endrule

  rule decodevlcintertable5 (videoSt == DecodeVLCInterTable5);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,5);
	Bit#(13)  decodedVLC = vlc_inter_table_5.sub(tmp[4:0]);
	Bool tmp_last;
	Bit#(6) tmp_run;
	Bit#(12) tmp_level;
	tmp_last = (decodedVLC[9] == 1);
	tmp_run =  zeroExtend(decodedVLC[8:4]);
	tmp_level = zeroExtend(decodedVLC[3:0]);
    if (flc_type == TYPE1)
	  tmp_level = tmp_level + flc.lmax(tmp_last,tmp_run,isIntra);
	else
	  tmp_level = tmp_level ;
	if (flc_type == TYPE2)
	   tmp_run = tmp_run + flc.rmax(tmp_last,tmp_level,isIntra);
	else
	   tmp_run = tmp_run ;
	flc_type <= NOTUSED;
	last <= tmp_last;
	run <= tmp_run;
	level <= tmp_level;
	byte_boundary <= byte_boundary + decodedVLC[12:10];
	byte_offset <= byte_offset - zeroExtend(decodedVLC[12:10]) ;
    //dct_coeff_cnt <= dct_coeff_cnt +  tmp_run + 1;
    dct_coeff_cnt <= dct_coeff_cnt +  tmp_run ;
    videoSt <= MB_BLK_STATE_12; 
  endrule

  rule decodevlcintertable6 (videoSt == DecodeVLCInterTable6);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,5);
	Bit#(14)  decodedVLC = vlc_inter_table_6.sub(tmp[4:0]);
	Bool tmp_last;
	Bit#(6) tmp_run;
	Bit#(12) tmp_level;
	tmp_last = (decodedVLC[10] == 1);
	tmp_run =  zeroExtend(decodedVLC[9:4]);
	tmp_level = zeroExtend(decodedVLC[3:0]);
    if (flc_type == TYPE1)
	  tmp_level = tmp_level + flc.lmax(tmp_last,tmp_run,isIntra);
	else
	  tmp_level = tmp_level ;
	if (flc_type == TYPE2)
	   tmp_run = tmp_run + flc.rmax(tmp_last,tmp_level,isIntra);
	else
	   tmp_run = tmp_run ;
	flc_type <= NOTUSED;
	last <= tmp_last;
	run <= tmp_run;
	level <= tmp_level;
	byte_boundary <= byte_boundary + decodedVLC[13:11];
	byte_offset <= byte_offset - zeroExtend(decodedVLC[13:11]) ;
    //dct_coeff_cnt <= dct_coeff_cnt +  tmp_run + 1;
    dct_coeff_cnt <= dct_coeff_cnt +  tmp_run ;
    videoSt <= MB_BLK_STATE_12; 
  endrule

  rule decodevlcintertable7 (videoSt == DecodeVLCInterTable7);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,3);
	Bit#(10)  decodedVLC = vlc_inter_table_7.sub(tmp[2:0]);
	Bool tmp_last;
	Bit#(6) tmp_run;
	Bit#(12) tmp_level;
	tmp_last = (decodedVLC[7] == 1);
	tmp_run =  zeroExtend(decodedVLC[6:3]);
	tmp_level = zeroExtend(decodedVLC[2:0]);
    if (flc_type == TYPE1)
	  tmp_level = tmp_level + flc.lmax(tmp_last,tmp_run,isIntra);
	else
	  tmp_level = tmp_level ;
	if (flc_type == TYPE2)
	   tmp_run = tmp_run + flc.rmax(tmp_last,tmp_level,isIntra);
	else
	   tmp_run = tmp_run ;
	flc_type <= NOTUSED;
	last <= tmp_last;
	run <= tmp_run;
	level <= tmp_level;
	byte_boundary <= byte_boundary + zeroExtend(decodedVLC[9:8]);
	byte_offset <= byte_offset - zeroExtend(decodedVLC[9:8]) ;
    //dct_coeff_cnt <= dct_coeff_cnt +  tmp_run + 1;
    dct_coeff_cnt <= dct_coeff_cnt +  tmp_run ;
    videoSt <= MB_BLK_STATE_12; 
  endrule

  rule decodevlcintertable8 (videoSt == DecodeVLCInterTable8);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,2);
	Bit#(9)  decodedVLC = vlc_inter_table_8.sub(tmp[1:0]);
	Bool tmp_last;
	Bit#(6) tmp_run;
	Bit#(12) tmp_level;
	tmp_last = (decodedVLC[6] == 1);
	tmp_run =  zeroExtend(decodedVLC[5:1]);
	tmp_level = zeroExtend(decodedVLC[0]);
    if (flc_type == TYPE1)
	  tmp_level = tmp_level + flc.lmax(tmp_last,tmp_run,isIntra);
	else
	  tmp_level = tmp_level ;
	if (flc_type == TYPE2)
	   tmp_run = tmp_run + flc.rmax(tmp_last,tmp_level,isIntra);
	else
	   tmp_run = tmp_run ;
	flc_type <= NOTUSED;
	last <= tmp_last;
	run <= tmp_run;
	level <= tmp_level;
	byte_boundary <= byte_boundary + zeroExtend(decodedVLC[8:7]);
	byte_offset <= byte_offset - zeroExtend(decodedVLC[8:7]) ;
    //dct_coeff_cnt <= dct_coeff_cnt +  tmp_run + 1;
    dct_coeff_cnt <= dct_coeff_cnt +  tmp_run ;
    videoSt <= MB_BLK_STATE_12; 
  endrule

  rule decodevlcintertable9 (videoSt == DecodeVLCInterTable9);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,2);
	Bit#(8)  decodedVLC = vlc_inter_table_9.sub(tmp[1:0]);
	Bool tmp_last;
	Bit#(6) tmp_run;
	Bit#(12) tmp_level;
	tmp_last = (decodedVLC[5] == 1);
	tmp_run =  zeroExtend(decodedVLC[4]);
	tmp_level = zeroExtend(decodedVLC[3:0]);
    if (flc_type == TYPE1)
	  tmp_level = tmp_level + flc.lmax(tmp_last,tmp_run,isIntra);
	else
	  tmp_level = tmp_level ;
	if (flc_type == TYPE2)
	   tmp_run = tmp_run + flc.rmax(tmp_last,tmp_level,isIntra);
	else
	   tmp_run = tmp_run ;
	flc_type <= NOTUSED;
	last <= tmp_last;
	run <= tmp_run;
	level <= tmp_level;
	byte_boundary <= byte_boundary + zeroExtend(decodedVLC[7:6]);
	byte_offset <= byte_offset - zeroExtend(decodedVLC[7:6]) ;
    //dct_coeff_cnt <= dct_coeff_cnt +  tmp_run + 1;
    dct_coeff_cnt <= dct_coeff_cnt +  tmp_run ;
    videoSt <= MB_BLK_STATE_12; 
  endrule

  rule check_resync_marker0 (videoSt == CHECK_RESYNC_MARKER0);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,1);
    if (byte_boundary == 0)
	  begin
	    if (byte_offset < 8)
		  begin
	        if (sysState == WAIT) 
		       begin
		         sysState <= START; 
		         vd_rd_reg <= 1'b1; 
                 videoSt <= CHECK_RESYNC_MARKER0_1_0; 
		       end
		    else
              videoSt <= CHECK_RESYNC_MARKER0_1; 
		    byte_offset <= byte_offset + 8;
		  end
		else
		  begin
	        if (sysState == START) 
		       begin
		         sysState <= WAIT; 
		         vd_rd_reg <= 1'b0; 
		         byte_offset <= byte_offset + 8;
		       end
		    else
		      byte_offset <= byte_offset ;
            videoSt <= CHECK_RESYNC_MARKER0_1; 
		  end
	  end
	else
	  begin
	    if (byte_offset >= 1)
	      begin
	        if (tmp[0] != 0)
		       begin
		         $display("current bits are not stuffing bits");
                 videoSt <= COMBINED_MST0; 
		       end
		    else
			  begin
                videoSt <= CHECK_RESYNC_MARKER; 
			  end
	         if (sysState == START) 
		       begin
		         sysState <= WAIT; 
		         vd_rd_reg <= 1'b0; 
		         byte_offset <= byte_offset + 8;
		       end
		     else
		       byte_offset <= byte_offset ;
	      end
	    else
		  begin
		    if (sysState == WAIT)
			  begin
		        sysState <= START; 
		        vd_rd_reg <= 1'b1; 
                videoSt <= CHECK_RESYNC_MARKER0_0; 
			  end
			else
              videoSt <= CHECK_RESYNC_MARKER0; 
		    byte_offset <= byte_offset + 8;
		  end
	  end
  endrule

  rule check_resync_marker0_0 (videoSt == CHECK_RESYNC_MARKER0_0);
    videoSt <= CHECK_RESYNC_MARKER0; 
	$display("wait_1_cycleCHECK_RESYNC_MARKER0_0 start code reg %h ",start_code_reg); 
  endrule

  rule check_resync_marker0_1_0 (videoSt == CHECK_RESYNC_MARKER0_1_0);
    videoSt <= CHECK_RESYNC_MARKER0_1; 
	$display("wait_1_cycleCHECK_RESYNC_MARKER0_1 start code reg %h ",start_code_reg); 
  endrule

  rule check_resync_marker0_1 (videoSt == CHECK_RESYNC_MARKER0_1);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8);
    if (tmp[7:0] == 8'h7f)
	  begin
	    $display("check_resync_marker0_1 state 7f detected");
	    if (sysState == START) 
		   begin
		     sysState <= WAIT; 
		     vd_rd_reg <= 1'b0; 
		     byte_offset <= byte_offset ;
		   end
		else
		  byte_offset <= byte_offset - 8;
	  end
	else
	  begin
	    if (sysState == START) 
		   begin
		     sysState <= WAIT; 
		     vd_rd_reg <= 1'b0; 
		     byte_offset <= byte_offset + 8;
		   end
		else
		  byte_offset <= byte_offset ;
	  end
    videoSt <= CHECK_RESYNC_MARKER; 
  endrule

  rule check_resync_marker (videoSt == CHECK_RESYNC_MARKER);
    Bit#(5) tmp_byte_boundary = (byte_boundary == 0) ? 0 : (8 - zeroExtend(byte_boundary)) ;
	Bit#(5) tmp_byte_offset = byte_offset - tmp_byte_boundary;
	if (byte_offset > tmp_byte_boundary)
	  begin
	    if ((tmp_byte_offset >= 7) && (sysState == START))
	      begin
		    sysState <= WAIT; 
		    vd_rd_reg <= 1'b0; 
            videoSt <= CHECK_RESYNC_MARKER1; 
		    byte_offset <= byte_offset + 8;
	        byte_offset_check <= byte_offset +8 - tmp_byte_boundary;
	      end
	    else if (tmp_byte_offset >= 15)
	      begin
            videoSt <= CHECK_RESYNC_MARKER1; 
	        if (sysState == START) 
		       begin
		         sysState <= WAIT; 
		         vd_rd_reg <= 1'b0; 
		         byte_offset <= byte_offset + 8;
	             byte_offset_check <= byte_offset +8 - tmp_byte_boundary;
		       end
		    else
		       begin
		         byte_offset <= byte_offset ;
	             byte_offset_check <= byte_offset - tmp_byte_boundary;
		       end
	      end
	    else
	      begin
	        if (sysState == WAIT) 
		       begin
		         sysState <= START; 
		         vd_rd_reg <= 1'b1; 
                 videoSt <= CHECK_RESYNC_MARKER_0; 
		       end
		    byte_offset <= byte_offset + 8;
	        byte_offset_check <= byte_offset +8 - tmp_byte_boundary;
	      end
	  end
	else
	  begin
	    if (sysState == WAIT) 
		  begin
		    sysState <= START; 
		    vd_rd_reg <= 1'b1; 
            videoSt <= CHECK_RESYNC_MARKER_0; 
		  end
		byte_offset <= byte_offset + 8;
	    byte_offset_check <= byte_offset +8 - tmp_byte_boundary;
	  end
  endrule

  rule check_resync_marker_0 (videoSt == CHECK_RESYNC_MARKER_0);
    videoSt <= CHECK_RESYNC_MARKER; 
	/*
	if ((byte_offset_check >= 15) && (sysState == START))
	  begin
		sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
	  end
	  */
	$display("wait_1_cycleCHECK_RESYNC_MARKER_0 start code reg %h ",start_code_reg); 
  endrule

  rule check_resync_marker1 (videoSt == CHECK_RESYNC_MARKER1);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset_check,15);
    if (tmp[14:0] != 0)
	  begin
	    //sysState <= WAIT; 
        //vd_rd_reg <= 1'b0; 
	    //byte_offset <= byte_offset + 8;
        videoSt <= COMBINED_MST0;
	  end
	else 
	  begin
	    if (byte_offset_check < 24)
		  begin
		    if (sysState == WAIT)
              videoSt <= CHECK_RESYNC_MARKER2_0; 
		    else
              videoSt <= CHECK_RESYNC_MARKER2; 
	        sysState <= START; 
            vd_rd_reg <= 1'b1; 
	        byte_offset <= byte_offset + 8;
	        byte_offset_check <= byte_offset_check + 8 - 15;
		  end
		else
		  begin
		    if (sysState == START)
		      begin
	            sysState <= WAIT; 
                vd_rd_reg <= 1'b0; 
	            byte_offset <= byte_offset + 8;
	            byte_offset_check <= byte_offset_check + 8 - 15;
		      end
		    else
		      begin
	            byte_offset <= byte_offset ;
	            byte_offset_check <= byte_offset_check - 15;
		      end
            videoSt <= CHECK_RESYNC_MARKER2; 
		  end
	  end
  endrule

  rule check_resync_marker_2_0 (videoSt == CHECK_RESYNC_MARKER2_0);
    if (byte_offset_check >= 9)
       videoSt <= CHECK_RESYNC_MARKER2; 
	else
	  byte_offset_check <= byte_offset_check + 8;
	$display("wait_1_cycleCHECK_RESYNC_MARKER2_0 start code reg %h ",start_code_reg); 
  endrule

  rule check_resync_marker2 ((videoSt == CHECK_RESYNC_MARKER2) && (vop_coding_type == 0));
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset_check,9);
    if (tmp[8:7] == 2'b01) 
		// Frame is I type and resync_marker detected 
	  begin
	    if (sysState == START)
		  begin
	        sysState <= WAIT; 
            vd_rd_reg <= 1'b0; 
	        byte_offset <= byte_offset_check -2 + 8  ;
		  end
	    else
	      byte_offset <= byte_offset_check -2   ;
        videoSt <= VIDEO_PACKET_HEADER; 
		$display("VIDEO_PACKET_HEADER detected");
		byte_boundary <= 1;
	  end
	else if (tmp[8:0] == 9'h001)  // start code detected
	  begin
	    if (sysState == START)
		  begin
	        sysState <= WAIT; 
            vd_rd_reg <= 1'b0; 
	        byte_offset <= byte_offset_check -9 + 8  ;
		  end
	    else
	      byte_offset <= byte_offset_check -9   ;
		$display("start code detected");
        videoSt <= START_CODE_DET; 
		byte_boundary <= 0;
	  end
	else
	  begin
	    sysState <= WAIT; 
        vd_rd_reg <= 1'b0; 
	    byte_offset <= byte_offset + 8;
        videoSt <= COMBINED_MST0;
	  end
  endrule

  rule check_resync_marker2_1 ((videoSt == CHECK_RESYNC_MARKER2) && (vop_coding_type == 1));
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset_check,tmp_vop_fcode_forward1[3:0]);
    if (tmp == 1) 
		// Frame is P type and resync_marker detected 
	  begin
	    if (sysState == START)
		  begin
	        sysState <= WAIT; 
            vd_rd_reg <= 1'b0; 
	        byte_offset <= byte_offset_check - tmp_vop_fcode_forward1 + 8  ;
		  end
	    else
	      byte_offset <= byte_offset_check - tmp_vop_fcode_forward1   ;
        videoSt <= VIDEO_PACKET_HEADER; 
		$display("VIDEO_PACKET_HEADER detected");
		byte_boundary <= tmp_vop_fcode_forward1[2:0] + 7;
	  end
	else if (tmp == 0)
	  begin
	    if (sysState == START)
		  begin
	        sysState <= WAIT; 
            vd_rd_reg <= 1'b0; 
	        byte_offset <= byte_offset + 8;
	        byte_offset_check <= byte_offset_check + 8;
		  end
	    else
		  begin
	        byte_offset <= byte_offset ;
	        byte_offset_check <= byte_offset_check ;
		  end
        videoSt <= CHECK_RESYNC_MARKER3;
	  end
	else
	  begin
	    if (sysState == START)
		  begin
	        sysState <= WAIT; 
            vd_rd_reg <= 1'b0; 
	        byte_offset <= byte_offset + 8;
		  end
	    else
	      byte_offset <= byte_offset ;
        videoSt <= COMBINED_MST0;
	  end
  endrule

  rule check_resync_marker3 (videoSt == CHECK_RESYNC_MARKER3);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset_check,9);
    if (tmp[8:0] == 9'h001)  //23 0's detected for P frame
	  begin
	    if (sysState == START)
		  begin
	        sysState <= WAIT; 
            vd_rd_reg <= 1'b0; 
	        byte_offset <= byte_offset_check - 9 + 8;
		  end
	    else
	      byte_offset <= byte_offset_check -9 ;
        videoSt <= START_CODE_DET; 
		byte_boundary <= 0;
	  end
	else 
	  begin
	    if (sysState == START)
		  begin
	        sysState <= WAIT; 
            vd_rd_reg <= 1'b0; 
	        byte_offset <= byte_offset + 8;
		  end
	    else
	      byte_offset <= byte_offset ;
        videoSt <= COMBINED_MST0;
		$display("Should never reach here ideally");
	  end
  endrule

    rule video_packet_header (videoSt == VIDEO_PACKET_HEADER);
    video_packet_header_detected <= True;
  	if (blkBuffer.busy == False) 
  	  begin
  	    if (isIntra || (!isIntra && (cbpc[0] == 1)))
  		 begin
  		  blkBuffer.sent_output_data(1'b1);
  		  pattern_code_d <= False;
  		  pattern_code_2d <= False;
	      $display("//////// Flushing last block in MB");
  		 end
          videoSt  <= VIDEO_PACKET_HEADER0; 
  	  end
    endrule

    rule video_packet_header0 (videoSt == VIDEO_PACKET_HEADER0);
    vop_mb_num_x <= 0;
    vop_mb_num_y <= 0;
	if (isIntra_d && (!isIntra_d && (cbpc[0] == 1)))
	  begin
        $display("clear signal");
	    blkBuffer.clear_d(1'b1); // send clear signal
	  end
    if (byte_offset < mb_bit_width)
	   begin 
	     if (sysState == WAIT) 
	       videoSt  <= VIDEO_PACKET_HEADER_1_0;
		 else 
           videoSt  <= VIDEO_PACKET_HEADER_1; 
		 sysState <= START; 
		 vd_rd_reg <= 1'b1; 
		 byte_offset <= byte_offset + 8;
	   end 
	else
       begin 
	     if (sysState == START) 
		    begin 
			  sysState <= WAIT; 
			  vd_rd_reg <= 1'b0; 
		      byte_offset <= byte_offset + 8;
		    end 
		 else 
		    byte_offset <= byte_offset ;
         videoSt  <= VIDEO_PACKET_HEADER_1; 
       end 
  endrule

  rule video_packet_header_1_0 (videoSt == VIDEO_PACKET_HEADER_1_0);
    videoSt <= VIDEO_PACKET_HEADER_1; 
	$display("wait_1_cycleVIDEO_PACKET_HEADER1_0 start code reg %h ",start_code_reg); 
  endrule

  rule video_packet_header_1 (videoSt == VIDEO_PACKET_HEADER_1);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,mb_bit_width[3:0]);
	$display("tmp = %h mb_bit_width = %d",tmp,mb_bit_width);
    macroblock_number <= tmp[8:0];
	byte_boundary <= byte_boundary + mb_bit_width[2:0];
	if (byte_offset < (mb_bit_width + 6))
	   begin 
	     if (sysState == WAIT) 
	       videoSt  <= VIDEO_PACKET_HEADER_2_0;
		 else 
           videoSt  <= VIDEO_PACKET_HEADER_2; 
		 sysState <= START; 
		 vd_rd_reg <= 1'b1; 
		 byte_offset <= byte_offset + 8 - mb_bit_width;
	   end 
	else
       begin 
	     if (sysState == START) 
		    begin 
			  sysState <= WAIT; 
			  vd_rd_reg <= 1'b0; 
		      byte_offset <= byte_offset + 8 - mb_bit_width;
		    end 
		 else 
		    byte_offset <= byte_offset  - mb_bit_width;
         videoSt  <= VIDEO_PACKET_HEADER_2; 
       end 
  endrule

  rule video_packet_header_2_0 (videoSt == VIDEO_PACKET_HEADER_2_0);
    videoSt <= VIDEO_PACKET_HEADER_2; 
	$display("wait_1_cycleVIDEO_PACKET_HEADER2_0 start code reg %h ",start_code_reg); 
  endrule

  rule video_packet_header_2 (videoSt == VIDEO_PACKET_HEADER_2);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,6);
    quant_scale <= tmp[5:1];
	// running QP has now been updated to quant_scale value
	running_QP <= zeroExtend(tmp[5:1]) ; 
    header_extension_code <= tmp[0];
	byte_boundary <= byte_boundary + 6;
	if (sysState == START) 
	  begin 
		sysState <= WAIT; 
		vd_rd_reg <= 1'b0; 
		byte_offset <= byte_offset + 8 - 6;
	  end 
	else 
	  byte_offset <= byte_offset  - 6;
    //videoSt  <= VOP_STATE_11; 
    if (data_partitioned == 1)
      videoSt  <= DATA_PARTITIONED_MST; // data partitioned motion shape texture
	else   
      videoSt  <= COMBINED_MST_0_2 ; // combined motion shape texture
  endrule

endrules;
return r;
endfunction
// *************************************************
// End of block7
// *************************************************

// *************************************************
// Start of block8
// Rules to write data into blkBuffer 
// and do AC/DC prediction
// *************************************************
function Rules create_block8 ();
 Rules r = rules
  rule acdcpred_0 (videoSt == MB_BLK_STATE);
    Bit#(12) leftblock;
    Bit#(12) topleftblock;
    Bit#(12) topblock;
    //Bit#(12) F_a,F_b,F_c,F_d,Fab,Fbc;
    Bit#(24) f_a;
    Bit#(24) f_b;
    Bit#(24) f_c;
    Bit#(24) fab;
    Bit#(24) fbc;
    Bit#(12) tmp_address;
    Bit#(12) tmp_cur_address;
	Bool     acpred_flag_a;
	Bool     acpred_flag_b;
	Bool     acpred_flag_c;
	Maybe#(Bit#(24)) leftblockvalue = Nothing;
	Maybe#(Bit#(24)) topleftblockvalue = Nothing;
	Maybe#(Bit#(24)) topblockvalue = Nothing;

	tmp_address = current_address;
	tmp_cur_address = current_address;

	if (((tmp_mb_num_x == 0) || 
	     ((tmp_vop_mb_num_y == 0) && (tmp_mb_num_x != 0) && (tmp_vop_mb_num_x == 0))) && 
	    !((vop_blk_num == 1) || (vop_blk_num ==3))
	   )
	  begin
	    leftblock = -1;
	    f_a = 24'd1024;
	    acpred_flag_a = False;
		$display("leftblock is -1 cond 1");
	  end
    else 
	  begin
	    if ((tmp_address == 0) && (vop_blk_num == 0))
		   leftblock = (3*tmp_mb_width - 1)*30 + 15;
	    else if ((tmp_address == (tmp_mb_width*30)) && (vop_blk_num == 2))
		   leftblock = (3*tmp_mb_width - 1)*30 + (2*tmp_mb_width + 1)*15;
	    else if ((tmp_address == (tmp_mb_width*60)) && (vop_blk_num == 0))
		   leftblock = tmp_mb_width *30  - 15;
	    else if ((tmp_address == (tmp_mb_width*90)) && (vop_blk_num == 2))
		   leftblock = tmp_mb_width *60  - 15;
		else if ((tmp_address == tmp_mb_width*120) && (vop_blk_num == 4))
		   leftblock = tmp_mb_width *150  - 15;
		else if ((tmp_address == tmp_mb_width*150) && (vop_blk_num == 5))
		   leftblock = tmp_mb_width *180  - 15;
		else
	      leftblock = tmp_address - 15;
		$display("leftblock is cond 2 leftblock = %d",leftblock);

             leftblockvalue = acdcPredBuffer.sub(leftblock);
	     if (isValid(leftblockvalue))
		begin
	           f_a = validValue(leftblockvalue);
		   acpred_flag_a = True;
		end
	     else
		  begin
	        leftblock = -1;
	        f_a = 24'd1024;
	        acpred_flag_a = False;
		    $display("leftblock is -1 cond 3 leftblock = %d",leftblock);
		  end
	  end

    if ((tmp_vop_mb_num_y == 0) && !((vop_blk_num ==2) || (vop_blk_num ==3)))
	  begin
	    topleftblock = -1;
	    topblock     = -1;
		$display("topblock & topleftblock is -1 cond 1 ");
	  end
    else if ((((tmp_vop_mb_num_x == 0) && (tmp_vop_mb_num_y == 0)) || (tmp_mb_num_x == 0))
			 && (vop_blk_num ==2))
	  begin
		topblock = tmp_address - tmp_mb_width*12'd30;
		if (tmp_mb_num_x !=0)
		  topleftblock = leftblock - tmp_mb_width*12'd30;
		else
		  begin
		    topleftblock = -1;
		    $display("topblock = %d topleftblock = %d cond 3 ",topblock,topleftblock);
		  end
		$display("topblock = %d topleftblock = %d cond 4 ",topblock,topleftblock);
	  end
    else if ((tmp_vop_mb_num_y == 0) && ((vop_blk_num == 2) ||  (vop_blk_num ==3)))
	  begin
		topblock = tmp_address - tmp_mb_width*12'd30;
		topleftblock = topblock - 15;
		$display("topblock = %d topleftblock = %d cond 5 ",topblock,topleftblock);
	  end
    else 
	  begin
	    if (tmp_vop_mb_num_y[0] == 1)
		   begin
		     if (vop_blk_num < 4)
			   begin
			     topblock = tmp_address - tmp_mb_width*12'd30;
				 topleftblock = topblock - 15;
			   end
		     else
			   begin
			     topblock = tmp_address - tmp_mb_width*12'd15;
				 topleftblock = topblock - 15;
			   end
		     $display("topblock = %d topleftblock = %d cond 6 ",topblock,topleftblock);
		   end
		else
		  begin
		    if (vop_blk_num < 2)
			  begin
			    topblock = tmp_address + tmp_mb_width*12'd90 ;
				topleftblock = topblock - 15;
			  end
		    else if (vop_blk_num < 4)
			  begin
			    topblock = tmp_address - tmp_mb_width*12'd30 ;
				topleftblock = topblock - 15;
			  end
		    else
			  begin
			    topblock = tmp_address + tmp_mb_width*12'd15 ;
				topleftblock = topblock - 15;
			  end
		     $display("topblock = %d topleftblock = %d cond 7 ",topblock,topleftblock);
		  end
		if (
		    (((vop_mb_num_y == 1) && (vop_mb_num_x == 0)) && 
			 ((vop_blk_num == 0) || (vop_blk_num == 4) || (vop_blk_num == 5))
			) ||  
		    ((tmp_mb_num_x == 0) && 
			 !((vop_blk_num == 1) || (vop_blk_num == 3))
			)
		   )
		    topleftblock = -1;
		else if ((topblock == 0) && (vop_blk_num < 4))
		  begin
		    topleftblock = tmp_mb_width*90 - 15;
		  end
		else if ((topblock == tmp_mb_width*30) && (vop_blk_num < 4))
		  begin
		    topleftblock = tmp_mb_width*120 - 15;
		  end
		else if ((topblock == tmp_mb_width*60) && (vop_blk_num < 4))
		  begin
		    topleftblock = tmp_mb_width*30 - 15;
		  end
		else if ((topblock == tmp_mb_width*90) && (vop_blk_num < 4))
		  begin
		    topleftblock = tmp_mb_width*60 - 15;
		  end
	    else
		    topleftblock = topleftblock;
		$display("topblock = %d topleftblock = %d cond 9 ",topblock,topleftblock);
	  end

	  topleftblockvalue = acdcPredBuffer.sub(topleftblock);
	  topblockvalue = acdcPredBuffer.sub(topblock);
	  if ((topleftblock != -1) && (isValid(topleftblockvalue)))
		begin
	        f_b = validValue(topleftblockvalue);
		    acpred_flag_b = True;
		end
	  else
		begin
	        topleftblock = -1;
	        f_b = 24'd1024;
	        acpred_flag_b = False;
		end
	  if ((topblock != -1) && (isValid(topblockvalue)))
		begin
	        f_c = validValue(topblockvalue);
		    acpred_flag_c = True;
		end
	  else
		begin
	        topblock = -1;
	        f_c = 24'd1024;
	        acpred_flag_c = False;
		end

	$display("leftblock %d topleftblock %d topblock %d address %d",leftblock,topleftblock,topblock,tmp_cur_address);

	fab = f_a - f_b;
	fbc = f_b - f_c;
	if (fab[23] == 1'b1)
	  fab = ~fab + 1;
	else
	  fab = fab ;
	if (fbc[23] == 1'b1)
	  fbc = ~fbc + 1;
	else
	  fbc = fbc ;
	if (fab < fbc)
	  begin
	    predicted_address <= topblock ;
		vertical_dir <= False;
		acpred_flag <= acpred_flag_c;
      end
	else
	  begin
	    predicted_address <= leftblock;
		vertical_dir <= True;
		acpred_flag <= acpred_flag_a;
      end
	acdcpredbuf_cur_addr <= tmp_cur_address;
	//if (isIntra && (short_video_header == False) && 
	//    !((vop_blk_num == 0) && (vop_mb_num_x == 0) && (vop_mb_num_y == 0)))
	if (isIntra && (short_video_header == False))
	  acDCPredRequired <= True;
	else
	  acDCPredRequired <= False;
  endrule

  rule acdcpred_1 ((videoSt == EXEC_ACDC_PREDICTION) && acDCPredRequired);
	Bit#(12) scaled_dc_ref_value ;
	Bit#(6) buf_addr ;
    if (acpred_flag)
	    scaled_dc_ref_value = 
		   division.div_func(validValue(acdcPredBuffer.sub(predicted_address)),zeroExtend(dc_scaler));
	else
	  scaled_dc_ref_value = division.div_func(24'd1024,zeroExtend(dc_scaler));
	$display("dc_scaler = %d scaled_dc_ref_value = %h",dc_scaler,scaled_dc_ref_value);
	Bit#(12) tmp_mem_data = blkBuffer.wr_data_read;
	dc_coeff <= signExtend(tmp_mem_data) + signExtend(scaled_dc_ref_value);
	//dc_coeff <= signExtend(blkBuffer.wr_data_read) + signExtend(scaled_dc_ref_value);
	videoSt <= EXEC_ACDC_PREDICTION1;
    if (vertical_dir)
	  begin
	    tmp_ac_addr <= predicted_address + 8;
	    buf_addr = 6'd8;
	  end
	else
	  begin
	   tmp_ac_addr <= predicted_address + 1;
	   buf_addr = 6'd1;
	  end
	blkBuffer.read_d(tuple2(1,buf_addr));
	tmp_buf_addr <= buf_addr;
  endrule

  rule acdcpred_2 ((videoSt == EXEC_ACDC_PREDICTION1) && acDCPredRequired);
	Bit#(12) scaled_ac_ref_value ;
	Bit#(6) buf_addr ;
	Bit#(16)  inverse_dc_quant = zeroExtend(dc_scaler) * dc_coeff;
	Bit#(12)  tmp_dc_coeff1 = inverse_quant.saturate(inverse_dc_quant);
	$display("inverse_dc_quant = %h tmp_dc_coeff = %h dc_coeff = %h",inverse_dc_quant,tmp_dc_coeff1,dc_coeff);
	blkBuffer.write_d(tuple3(1,0,tmp_dc_coeff1));
	acdcPredBuffer.upd(acdcpredbuf_cur_addr,Just(signExtend(tmp_dc_coeff1)));
	$display("writing acdcPredBuffer addr = %d data = %h",acdcpredbuf_cur_addr,tmp_dc_coeff1);
	if ((ac_pred_flag == 1) && acpred_flag)
	    scaled_ac_ref_value = division.div_func(validValue(acdcPredBuffer.sub(tmp_ac_addr)),running_QP[11:0]);
	    //scaled_ac_ref_value = acdcPredBuffer.sub(tmp_ac_addr);
    else
	    scaled_ac_ref_value = 0;
	tmp_ac_addr <= tmp_ac_addr + 1;
	acdcpredbuf_cur_addr <= acdcpredbuf_cur_addr + 1;
    if (vertical_dir)
	  buf_addr = tmp_buf_addr + 8;
	else
	  buf_addr = tmp_buf_addr + 1;
	blkBuffer.read_d(tuple2(1,buf_addr));
	tmp_buf_addr <= buf_addr;
    ac_coeff <= blkBuffer.wr_data_read + scaled_ac_ref_value;
	/**************************************************************
	if (acpred_flag)
	  begin
	    videoSt <= EXEC_ACDC_PREDICTION2;
		acdcpred_cnt <= 0;
	  end
    else
	  begin
	    videoSt <= MB_BLK_STATE_12;
		acDCPredDone <= True;
	  end
	  *************************************************************/
	videoSt <= EXEC_ACDC_PREDICTION2;
	acdcpred_cnt <= 0;
  endrule

// Need to do inverse quantisation of ac coeffiecients here
  rule acdcpred_3 (((videoSt == EXEC_ACDC_PREDICTION2) && (acdcpred_cnt < 7)) && acDCPredRequired);
	Bit#(12) scaled_ac_ref_value ;
	Bit#(12) inverse_quantised_dct_data ;
	Bit#(6)  buf_addr = vertical_dir ? (tmp_buf_addr - 8) : (tmp_buf_addr - 1);
    Bit#(12) absolute_ac_coeff_value = (ac_coeff[11] == 1) ? (~ac_coeff + 1) : ac_coeff;

	// do inverse quantization of ac_coeff
	if (quant_type == 1)
	  inverse_quantised_dct_data = 
	         inverse_quant.getmethod1(ac_coeff[11],isIntra,ac_coeff,running_QP,weighting_matrix);
    else
	     begin
	        $display("method2 is chosen sign = %d level = %h QP = %d",ac_coeff[11],absolute_ac_coeff_value,running_QP);
	  inverse_quantised_dct_data = 
	         inverse_quant.getmethod2(ac_coeff[11],absolute_ac_coeff_value,running_QP);
		 end
    if (pattern_code)
	  begin
	    $display("inverse_dct_quant = %h ac_coeff = %h buf_addr = %d ",inverse_quantised_dct_data,ac_coeff,tmp_buf_addr);
	    blkBuffer.write_d(tuple3(1,buf_addr,inverse_quantised_dct_data));
	     Bit#(24) tmp_data = signExtend(inverse_quantised_dct_data)*zeroExtend(running_QP[11:0]) ;
	    acdcPredBuffer.upd(acdcpredbuf_cur_addr,Just(tmp_data));
	    $display("writing acdcPredBuffer addr = %d data = %h",acdcpredbuf_cur_addr,tmp_data);
	  end
    else
	  begin
	    acdcPredBuffer.upd(acdcpredbuf_cur_addr,Just(0));
	    $display("writing acdcPredBuffer addr = %d data = 0",acdcpredbuf_cur_addr);
	  end
	acdcpredbuf_cur_addr <= acdcpredbuf_cur_addr + 1;

	if ((ac_pred_flag == 1) && acpred_flag)
	    scaled_ac_ref_value = division.div_func(validValue(acdcPredBuffer.sub(tmp_ac_addr)),running_QP[11:0]);
	    //scaled_ac_ref_value = acdcPredBuffer.sub(tmp_ac_addr);
    else
	    scaled_ac_ref_value = 0;
    ac_coeff <= blkBuffer.wr_data_read + scaled_ac_ref_value;
	if (acdcpred_cnt != 6)
	  begin
	    videoSt <= EXEC_ACDC_PREDICTION2;
	    acdcpred_cnt <= acdcpred_cnt + 1;
        if (vertical_dir)
	      buf_addr = tmp_buf_addr + 8;
	    else
	      buf_addr = tmp_buf_addr + 1;
	    blkBuffer.read_d(tuple2(1,buf_addr));
	  end
    else
	  begin
	    videoSt <= EXEC_ACDC_PREDICTION3;
		if (vertical_dir)
		  begin
		    tmp_ac_addr <= predicted_address + 1;
			buf_addr = 1;
	      end
		else
		  begin
		    tmp_ac_addr <= predicted_address + 8;
			buf_addr = 8;
	      end
	    acdcpred_cnt <= 0;
	    blkBuffer.read_d(tuple2(1,buf_addr));
	  end
	tmp_buf_addr <= buf_addr;
  endrule

  rule acdcpred_4 (((videoSt == EXEC_ACDC_PREDICTION3) && (acdcpred_cnt < 7)) && acDCPredRequired);
	blkBuffer.read_d(tuple2(1,tmp_buf_addr));
	Bit#(24) tmp_data = signExtend(blkBuffer.wr_data_read)*signExtend(running_QP[11:0]) ;
	if (pattern_code)
	  begin
	    acdcPredBuffer.upd(acdcpredbuf_cur_addr,Just(tmp_data));
	    $display("writing acdcPredBuffer addr = %d data = %h",acdcpredbuf_cur_addr,tmp_data);
	  end
	else
	  begin
	    acdcPredBuffer.upd(acdcpredbuf_cur_addr,Just(0));
	    $display("writing acdcPredBuffer addr = %d data = 0",acdcpredbuf_cur_addr);
	  end
	acdcpredbuf_cur_addr <= acdcpredbuf_cur_addr + 1;
    if (vertical_dir)
	  tmp_buf_addr <= tmp_buf_addr + 1;
	else
	  tmp_buf_addr <= tmp_buf_addr + 8;
	if (acdcpred_cnt != 6)
	  acdcpred_cnt <= acdcpred_cnt + 1;
	else
	  begin
	    videoSt <= MB_BLK_STATE_12;
		acDCPredDone <= True;
	  end
  endrule

  rule acdcpred_inter1 ((videoSt == EXEC_ACDC_PREDICTION) && !acDCPredRequired);
	acdcPredBuffer.upd(acdcpredbuf_cur_addr,Nothing);
	//$display("writing acdcPredBuffer addr = %d data = Nothing",acdcpredbuf_cur_addr);
	acdcpredbuf_cur_addr <= acdcpredbuf_cur_addr + 1;
	acdcpred_cnt <= 1;
	videoSt <= EXEC_ACDC_PREDICTION_INTER;
  endrule

  rule acdcpred_inter2 ((videoSt == EXEC_ACDC_PREDICTION_INTER) && (acdcpred_cnt < 15));
	acdcPredBuffer.upd(acdcpredbuf_cur_addr,Nothing);
	//$display("writing acdcPredBuffer addr = %d data = Nothing",acdcpredbuf_cur_addr);
	acdcpredbuf_cur_addr <= acdcpredbuf_cur_addr + 1;
	if (acdcpred_cnt != 14)
	  acdcpred_cnt <= acdcpred_cnt + 1;
	else
	  begin
	    videoSt <= MB_BLK_STATE_12;
		acDCPredDone <= True;
	    acdcpred_cnt <= 0;
	  end
  endrule

  rule start_code_flush_blkbuffer (videoSt == START_CODE_DET);
    start_code_detected <= True;
	if (blkBuffer.busy == False)
	  begin
	    if ((!isIntra && cbpc[0] == 1) || isIntra)
		  blkBuffer.sent_output_data(1'b1);
        videoSt  <= START_CODE_DET0; 
	  end
  endrule

  rule start_code_det00 (videoSt == START_CODE_DET0);
	if ((!isIntra && cbpc[0] == 1) || isIntra)
	  begin
        $display("clear signal");
	    blkBuffer.clear_d(1'b1); // send clear signal
	  end
	if (byte_offset < 8) 
	  begin 
		if (sysState == WAIT) 
		   videoSt  <= START_CODE_DET_1_0; 
		else 
		   videoSt  <= START_CODE_DET_1; 
		byte_offset <= byte_offset + 8 ; 
		sysState <= START; 
		vd_rd_reg <= 1'b1; 
	  end 
	else
	  begin 
		if (sysState == START)
		  begin
			vd_rd_reg <= 1'b0; 
			byte_offset <= byte_offset + 8  ; 
			sysState <= WAIT; 
		  end
		else
		  byte_offset <= byte_offset ; 
	    videoSt  <= START_CODE_DET_1; 
	  end 
  endrule

  rule start_code_det_1_0 (videoSt == START_CODE_DET_1_0);
    videoSt <= START_CODE_DET_1; 
	$display("wait_1_cycleSTART_CODE_1 start code reg %h ",start_code_reg); 
  endrule

  rule start_code_det_1 (videoSt == START_CODE_DET_1);
    Bit#(16) tmp = byteAlign.get(start_code_reg,byte_offset,8); 
	if (tmp[7:0] <= 8'h1F)
	  begin
	    videoSt <= VIDEO_OBJECT_LAYER1;
		cnt <= 0;
	    $display("video object start code detected");
	  end
	else if (tmp[7:0] <= 8'h2F)
	  begin
	    videoSt <= VIDEO_OBJECT_LAYER2;
	    $display("video object layer start code detected");
	  end
	else if (tmp[7:0] == 8'hB2)
	  begin
	    //videoSt <= USER_DATA;
	    $display("Error :: user data start code detected");
	  end
	else if (tmp[7:0] == 8'hB3)
	  begin
	    videoSt <= GROUP_OF_VOP;
	    $display("group of vop start code detected");
		vop_start_code_detected <= True;
	  end
	else if (tmp[7:0] == 8'hB6)
	  begin
	    videoSt <= VOP_STATE_0;
	    $display("vop start code detected");
		vop_start_code_detected <= True;
	  end
	else
	  begin
	    $display("Error Error NO start code detected");
	  end
	if (sysState == START)
	  begin
		vd_rd_reg <= 1'b0; 
		byte_offset <= byte_offset ; 
		sysState <= WAIT; 
	  end
	else
	  byte_offset <= byte_offset -8 ; 
	byte_boundary <= 0;
  endrule

  rule vop_state_0 (videoSt == VOP_STATE_0);
	if (byte_offset < 2) 
	   begin 
		 if (sysState == WAIT) 
		   videoSt  <= VOP_STATE_0_1; 
		 else 
		   videoSt  <= VOP_STATE; 
		 byte_offset <= byte_offset + 8 ; 
	     sysState <= START; 
		 vd_rd_reg <= 1'b1; 
	   end 
     else
	   begin 
		 if (sysState == START)
		   begin
			 vd_rd_reg <= 1'b0; 
			 byte_offset <= byte_offset + 8  ; 
			 sysState <= WAIT; 
		   end
		 else
		   byte_offset <= byte_offset ; 
		 videoSt  <= VOP_STATE; 
	   end 
  endrule

  rule vop_state_0_1 (videoSt == VOP_STATE_0_1);
    videoSt <= VOP_STATE; 
	$display("wait_1_cycleVOP_STATE start code reg %h ",start_code_reg); 
  endrule

endrules;
return r;
endfunction
// *************************************************
// End of block8
// *************************************************

  Rules block00 = create_block0;
  Rules block01 = create_block1;
  Rules block02 = create_block2;
  Rules block03 = create_block3;
  Rules block04 = create_block4;
  Rules block05 = create_block5;
  Rules block06 = create_block6;
  Rules block07 = create_block7;
  Rules block08 = create_block8;

  List#(Rules) my_list = Cons (block00, Cons (block01, Cons (block02, 
                         Cons (block03, Cons (block04, Cons (block05, 
						 Cons (block06, Cons (block07, Cons (block08,nil)))))))));

  addRules (joinRules (my_list)) ;

  method get_host_strobe (x); 
    action 
	  host_strobe.wset(x); 
	endaction 
  endmethod : get_host_strobe 
  
  method get_host_select (x); 
    action 
	  host_select.wset(x);
    endaction 
  endmethod : get_host_select 
  
  method get_host_address (x); 
    action
      host_address.wset(x); 
	endaction 
  endmethod : get_host_address 
  
  method get_host_datain (x); 
    action 
	  host_datain.wset(x); 
    endaction 
  endmethod : get_host_datain 
  
  method get_vd_valid (x); 
    action 
	  vd_valid.wset(x); 
    endaction
  endmethod : get_vd_valid 
  
  method get_vd_data (x); 
    action 
	  vd_data.wset(x);
    endaction 
  endmethod : get_vd_data 
  
  method get_rdmv (x); 
    action 
	  rdmv.wset(x);
    endaction 
  endmethod : get_rdmv 
  
  method get_mb_done (x); 
    action 
	  mb_done.wset(x);
    endaction 
  endmethod : get_mb_done 
  
  method vd_rd (); 
    vd_rd = vd_rd_reg;
  endmethod : vd_rd 
  
  method dct_data_out (); 
    dct_data_out = blkBuffer.data_out;
  endmethod : dct_data_out 
  
  method dct_data_valid (); 
    dct_data_valid = blkBuffer.data_valid;
  endmethod : dct_data_valid 
  
  method hdr_rdy (); 
    hdr_rdy = (mbheaderfifo.notEmpty == True) ? 1'b1 : 1'b0;
  endmethod : hdr_rdy 
  
  method busy (); 
    busy = ((videoSt != IDLE) || (videoSt != SUSPEND));
  endmethod : busy 
  
  method vop_done (); 
    vop_done = vop_start_code_detected;
  endmethod : vop_done 
  
  method disable_mb_done (); 
    disable_mb_done = disable_mb_done_reg;
  endmethod : disable_mb_done 
  
  method header_data ();
    header_data = mbhdrdata_reg;
  endmethod : header_data 

  /*
  method mb_coded (); 
    mb_coded = not_coded;
  endmethod : mb_coded
  */
  
endmodule : mkBtStrmPrsr

endpackage : BtStrmPrsr
