// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.


  bit error_event, error_event_xz;

`ifdef OVL_ASSERT_ON

  always @(posedge clk)
  begin
    error_event = 0;
    error_event_xz = 0;
  end

`endif // OVL_ASSERT_ON

`ifdef OVL_REVISIT // Tied low in V2.3 (in top-level file)
  `ifdef OVL_ASSERT_ON
    assign fire[0] = error_event;
    assign fire[1] = error_event_xz;
  `else
    assign fire[0] = 1'b0;
    assign fire[1] = 1'b0;
  `endif // OVL_ASSERT_ON

  `ifdef OVL_COVER_ON
    assign fire[2] = 1'b0;
  `else
    assign fire[2] = 1'b0;
  `endif // OVL_COVER_ON
`endif // OVL_REVISIT

  genvar i;

`ifdef OVL_SHARED_CODE

  localparam          latency_bw                 = log2(max_cks);
  localparam          max_instances_per_id_bw    = log2(max_instances_per_id);
  localparam          max_id_instances_bw        = log2(max_id_instances);

  wire                sva_v_issued;
  wire                sva_v_ret;

  wire  [1:max_id_instances]          sva_v_valid_arr; // valid entries
  wire  [max_instances_per_id_bw-1:0] sva_v_issued_arr[1:max_id_instances]; //nb of issued
  // compute the index of the entry in the associative arrays
  wire  [max_id_instances_bw-1:0] sva_v_issued_entry_tmp[1:max_id_instances]; //issued entry
  wire  [max_id_instances_bw-1:0] sva_v_issued_entry;
  wire  [max_id_instances_bw-1:0] sva_v_ret_entry_tmp[1:max_id_instances]; //ret entry
  wire  [max_id_instances_bw-1:0] sva_v_ret_entry;
  wire  [max_id_instances_bw-1:0] sva_v_free_entry_tmp[1:max_id_instances]; //available entry
  wire  [max_id_instances_bw-1:0] sva_v_free_entry;
  wire  [max_id_instances_bw-1:0] sva_v_rst_entry_tmp[1:max_id_instances]; //reset entry
  wire  [max_id_instances_bw-1:0] sva_v_rst_entry;
  wire  [max_id_instances_bw-1:0] sva_v_outstanding_ids_tmp[1:max_id_instances]; //nb of id's out
  wire  [max_id_instances_bw-1:0] sva_v_outstanding_ids;

  reg   [width-1:0]             sva_v_issued_id[1:max_id_instances]; // active id's
  reg   [max_instances_per_id_bw-1:0] sva_v_iss_cnt  [1:max_id_instances]; // count issues - tail pointers
  reg   [max_instances_per_id_bw-1:0] sva_v_ret_cnt  [1:max_id_instances]; // count ret's - head pointers

  reg   [latency_bw:0]          sva_v_clock_count; // current time

  // array of time stamps for each issued and id
  reg   [latency_bw:0]          sva_v_queue[1:max_id_instances][0:(1<<max_instances_per_id_bw)-1];

  // count required returns, will be initialized to issued_count upon issued
  reg   [instance_count_width-1:0]        sva_v_cnt_ret [1:max_id_instances][0:(1<<max_instances_per_id_bw)-1];

  wire  [latency_bw:0]          sva_v_delay; // current delay from issued to ret
  reg   [latency_bw:0]          sva_v_queue_head;
  reg                           sva_v_valid_simultaneous_iss_ret;
  reg                           sva_v_empty;

  wire                          sva_v_iss_rst_entry; //issued == reset entry
  wire                          sva_v_ret_rst_entry; //ret == reset entry
  wire                          sva_v_iss_returned_id; //issued_id == returned_id
  wire                          sva_v_iss_rst_id; //issued_id == flush_id
  wire  [max_instances_per_id_bw-1:0]   sva_v_current_out; //issued_id nb of out
  wire  [1:max_id_instances]             sva_v_max_cksency_ok;
  reg   [1:max_id_instances]         sva_v_block_lat_chk;

  integer k;
  assign sva_v_issued = issued   && `OVL_RESET_SIGNAL;
  assign sva_v_ret    = returned && `OVL_RESET_SIGNAL;

`ifdef OVL_SYNTHESIS
`else
  initial begin
         for ( k=1; k<= max_id_instances; k=k+1) begin
             sva_v_issued_id[k] = 0;
             sva_v_iss_cnt[k]   = 0;
             sva_v_ret_cnt[k]   = 0;
          end
          sva_v_clock_count = 0;
      sva_v_block_lat_chk = 0;

         end
`endif
 
   generate
   for ( i=1; i<=max_id_instances; i=i+1) begin : loop_max_id_instances0
           assign sva_v_issued_arr[i] =  // compute number of outstanding issues
             ( sva_v_iss_cnt[i] >= sva_v_ret_cnt[i] ) ?
               ( sva_v_iss_cnt[i] - sva_v_ret_cnt[i] ) :
               ( {1'b1,sva_v_iss_cnt[i]} - {1'b0, sva_v_ret_cnt[i]});

           assign sva_v_valid_arr[i] = ( sva_v_issued_arr[i] > 0 ); // valid entry
         end : loop_max_id_instances0
         assign sva_v_current_out = sva_v_issued_entry ?  //nb outs
                                        sva_v_issued_arr[sva_v_issued_entry] : 0;

  endgenerate

       assign sva_v_issued_entry_tmp[1] = // compute issued entry index in array
           !sva_v_valid_arr[1] ? 0 :
             ( sva_v_issued_id[1] == issued_id ) ? 1 : 0;

       generate
         for ( i=2; i<=max_id_instances; i=i+1) begin : loop_max_id_instances1
           assign sva_v_issued_entry_tmp[i] =
             ( sva_v_issued_entry_tmp[i-1] != 0 ) ?
               sva_v_issued_entry_tmp[i-1] :
                 !sva_v_valid_arr[i] ? 0 :
                   ( sva_v_issued_id[i] == issued_id ) ? i : 0;
         end : loop_max_id_instances1

       endgenerate

       assign sva_v_issued_entry = sva_v_issued_entry_tmp[max_id_instances]; // issued entry

       assign sva_v_ret_entry_tmp[1] = // compute return entry index
           !sva_v_valid_arr[1] ? 0 :
             ( sva_v_issued_id[1] == returned_id ) ? 1 : 0;

       generate
         for ( i=2; i<=max_id_instances; i=i+1) begin : loop_max_id_instances2
           assign sva_v_ret_entry_tmp[i] =
             ( sva_v_ret_entry_tmp[i-1] != 0 ) ?
               sva_v_ret_entry_tmp[i-1] :
               !sva_v_valid_arr[i] ? 0 :
                 ( sva_v_issued_id[i] == returned_id ) ? i : 0;
         end : loop_max_id_instances2
       endgenerate

       assign sva_v_ret_entry = sva_v_ret_entry_tmp[max_id_instances]; // current return entry

       assign sva_v_free_entry_tmp[1] = // nearest free entry index
           sva_v_valid_arr[1] ? 0 : 1;

       generate
         for ( i=2; i<=max_id_instances; i=i+1) begin : loop_max_id_instances3
           assign sva_v_free_entry_tmp[i] =
             ( sva_v_free_entry_tmp[i-1] != 0 ) ?
               sva_v_free_entry_tmp[i-1] :
               sva_v_valid_arr[i] ? 0 : i;
         end : loop_max_id_instances3
       endgenerate

       assign sva_v_free_entry = sva_v_free_entry_tmp[max_id_instances]; // free entry index

       assign sva_v_rst_entry_tmp[1] = // compute rst entry index
           !sva_v_valid_arr[1] ? 0 :
             ( sva_v_issued_id[1] == flush_id ) ? 1 : 0;

       generate
         for ( i=2; i<=max_id_instances; i=i+1) begin : loop_max_id_instances4
           assign sva_v_rst_entry_tmp[i] =
             ( sva_v_rst_entry_tmp[i-1] != 0 ) ?
               sva_v_rst_entry_tmp[i-1] :
                 !sva_v_valid_arr[i] ? 0 :
                   ( sva_v_issued_id[i] == flush_id ) ? i : 0;
         end : loop_max_id_instances4
       endgenerate

       assign sva_v_rst_entry = sva_v_rst_entry_tmp[max_id_instances]; // current rst entry index

       assign sva_v_outstanding_ids_tmp[1] = // compute # of issued ids
                                sva_v_valid_arr[1] ? 1 : 0;

       generate
         for ( i=2; i<=max_id_instances; i=i+1) begin : loop_max_id_instances5
           assign sva_v_outstanding_ids_tmp[i] =
              sva_v_valid_arr[i] ?
               sva_v_outstanding_ids_tmp[i-1]+1 :
                sva_v_outstanding_ids_tmp[i-1];
         end : loop_max_id_instances5
       endgenerate

       assign sva_v_outstanding_ids =
                         sva_v_outstanding_ids_tmp[max_id_instances]; // current id's out
       assign sva_v_iss_rst_entry =
                         (sva_v_issued_entry == sva_v_rst_entry);//matching entries
       assign sva_v_ret_rst_entry = (sva_v_ret_entry == sva_v_rst_entry);
       assign sva_v_iss_returned_id = issued_id == returned_id; // matching id's
       assign sva_v_iss_rst_id = issued_id == flush_id;

      always @(posedge clk ) begin

         if(`OVL_RESET_SIGNAL==1'b0)
           for( k = 1; k <= max_id_instances; k=k+1 ) begin
             sva_v_iss_cnt[k]    <= 0;
             sva_v_ret_cnt[k]    <= 0;
             sva_v_issued_id[k]  <= 0;
         sva_v_clock_count   <= 0;
             sva_v_block_lat_chk <= 0;
           end
         else begin
           sva_v_clock_count <= (sva_v_clock_count + {{latency_bw{1'b0}}, 1'b1});

       for( k = 1; k <= max_id_instances; k=k+1 )
             sva_v_block_lat_chk[k] <= (sva_v_block_lat_chk[k] ||
                                  (sva_v_valid_arr[k] && !sva_v_max_cksency_ok[k])
                                  ) &&
                                 !(
                                   returned && (sva_v_ret_entry == k) ||
                                   flush && (sva_v_rst_entry == k)
                                  );

           case({issued,returned,flush})

           1: if(sva_v_rst_entry) begin // rst only
                sva_v_iss_cnt[sva_v_rst_entry] <= 0;
                sva_v_ret_cnt[sva_v_rst_entry] <= 0;
              end

           2: if(sva_v_ret_entry) // ret only
                if(sva_v_cnt_ret[sva_v_ret_entry][sva_v_ret_cnt[sva_v_ret_entry]] == 1)
                begin
                  sva_v_ret_cnt[sva_v_ret_entry] <= sva_v_ret_cnt[sva_v_ret_entry]+1;
                end
                else begin
                  sva_v_cnt_ret[sva_v_ret_entry][sva_v_ret_cnt[sva_v_ret_entry]]
                     <= sva_v_cnt_ret[sva_v_ret_entry][sva_v_ret_cnt[sva_v_ret_entry]]-1;
                end

           3: begin  // ret and rst
                if(sva_v_rst_entry) begin
                  sva_v_iss_cnt[sva_v_rst_entry] <= 0;
                  sva_v_ret_cnt[sva_v_rst_entry] <= 0;
                end
                if(sva_v_ret_entry && !sva_v_ret_rst_entry)
                  if(sva_v_cnt_ret[sva_v_ret_entry][sva_v_ret_cnt[sva_v_ret_entry]] == 1)
                  begin
                    sva_v_ret_cnt[sva_v_ret_entry] <= sva_v_ret_cnt[sva_v_ret_entry]+1;
                  end
                  else begin
                    sva_v_cnt_ret[sva_v_ret_entry][sva_v_ret_cnt[sva_v_ret_entry]]
                      <= sva_v_cnt_ret[sva_v_ret_entry][sva_v_ret_cnt[sva_v_ret_entry]]-1;
                  end
              end

           4: if(sva_v_issued_entry &&
                   (sva_v_current_out < max_instances_per_id) && (issued_count > 0 )) begin // issued only
                sva_v_iss_cnt[sva_v_issued_entry] <=
                                                 sva_v_iss_cnt[sva_v_issued_entry] + 1;
                sva_v_queue[sva_v_issued_entry][sva_v_iss_cnt[sva_v_issued_entry]]
                  <= sva_v_clock_count;
                sva_v_cnt_ret[sva_v_issued_entry][sva_v_iss_cnt[sva_v_issued_entry]]
                  <= issued_count;
              end
              else if(!sva_v_issued_entry && sva_v_free_entry && (issued_count > 0)) begin
                sva_v_iss_cnt[sva_v_free_entry] <= sva_v_iss_cnt[sva_v_free_entry] + 1;
                sva_v_issued_id[sva_v_free_entry] <= issued_id;
                sva_v_queue[sva_v_free_entry][sva_v_iss_cnt[sva_v_free_entry]]
                  <= sva_v_clock_count;
                sva_v_cnt_ret[sva_v_free_entry][sva_v_iss_cnt[sva_v_free_entry]]
                  <= issued_count;
              end

           5: begin   // issued and rst
                if(sva_v_rst_entry) begin
                  sva_v_iss_cnt[sva_v_rst_entry] <= 0;
                  sva_v_ret_cnt[sva_v_rst_entry] <= 0;
                end
                if(sva_v_issued_entry && !sva_v_iss_rst_id &&
                   (sva_v_current_out < max_instances_per_id)) begin
                  sva_v_iss_cnt[sva_v_issued_entry]
                    <= sva_v_iss_cnt[sva_v_issued_entry] + 1;
                  sva_v_queue[sva_v_issued_entry][sva_v_iss_cnt[sva_v_issued_entry]]
                    <= sva_v_clock_count;
                  sva_v_cnt_ret[sva_v_issued_entry][sva_v_iss_cnt[sva_v_issued_entry]]
                    <= issued_count;
                end else
                if(!sva_v_issued_entry && sva_v_free_entry) begin
                  sva_v_iss_cnt[sva_v_free_entry] <= sva_v_iss_cnt[sva_v_free_entry] + 1;
                  sva_v_issued_id[sva_v_free_entry] <= issued_id;
                  sva_v_queue[sva_v_free_entry][sva_v_iss_cnt[sva_v_free_entry]]
                    <= sva_v_clock_count;
                  sva_v_cnt_ret[sva_v_free_entry][sva_v_iss_cnt[sva_v_free_entry]]
                    <= issued_count;
                end
              end

           6: begin // issued and ret
                if(sva_v_issued_entry) begin
                  if(sva_v_iss_returned_id ||
                    sva_v_current_out < max_instances_per_id) begin
                    sva_v_iss_cnt[sva_v_issued_entry]
                      <= sva_v_iss_cnt[sva_v_issued_entry] + 1;
                    sva_v_queue[sva_v_issued_entry][sva_v_iss_cnt[sva_v_issued_entry]]
                      <= sva_v_clock_count;
                    sva_v_cnt_ret[sva_v_issued_entry][sva_v_iss_cnt[sva_v_issued_entry]]
                      <= issued_count;
                  end
                end else
                if(!sva_v_iss_returned_id || !(min_cks == 0))
                  if(sva_v_free_entry && !sva_v_iss_returned_id ) begin
                    sva_v_iss_cnt[sva_v_free_entry] <= sva_v_iss_cnt[sva_v_free_entry] + 1;
                    sva_v_issued_id[sva_v_free_entry] <= issued_id;
                    sva_v_queue[sva_v_free_entry][sva_v_iss_cnt[sva_v_free_entry]]
                      <= sva_v_clock_count;
                    sva_v_cnt_ret[sva_v_free_entry][sva_v_iss_cnt[sva_v_free_entry]]
                      <= issued_count;
                  end
                if(sva_v_ret_entry)
                  if(sva_v_cnt_ret[sva_v_ret_entry][sva_v_ret_cnt[sva_v_ret_entry]] == 1)
                  begin
                    sva_v_ret_cnt[sva_v_ret_entry] <= sva_v_ret_cnt[sva_v_ret_entry]+1;
                  end
                  else begin
                    sva_v_cnt_ret[sva_v_ret_entry][sva_v_ret_cnt[sva_v_ret_entry]]
                      <= sva_v_cnt_ret[sva_v_ret_entry][sva_v_ret_cnt[sva_v_ret_entry]] - 1;
                  end

              end

           7: begin // issued and ret and rst
                if(sva_v_rst_entry) begin
                  sva_v_iss_cnt[sva_v_rst_entry] <= 0;
                  sva_v_ret_cnt[sva_v_rst_entry] <= 0;
                end
                if(sva_v_issued_entry) begin
                  if(!sva_v_iss_rst_id && (sva_v_iss_returned_id ||
                    sva_v_current_out < max_instances_per_id)) begin
                    sva_v_iss_cnt[sva_v_issued_entry]
                      <= sva_v_iss_cnt[sva_v_issued_entry] + 1;
                    sva_v_queue[sva_v_issued_entry][sva_v_iss_cnt[sva_v_issued_entry]]
                      <= sva_v_clock_count;
                    sva_v_cnt_ret[sva_v_issued_entry][sva_v_iss_cnt[sva_v_issued_entry]]
                      <= issued_count;
                  end
                end else
                if(!sva_v_iss_returned_id || !(min_cks == 0) )
                  if(sva_v_free_entry) begin
                    sva_v_iss_cnt[sva_v_free_entry]
                      <= sva_v_iss_cnt[sva_v_free_entry] + 1;
                    sva_v_issued_id[sva_v_free_entry] <= issued_id;
                    sva_v_queue[sva_v_free_entry][sva_v_iss_cnt[sva_v_free_entry]]
                      <= sva_v_clock_count;
                    sva_v_cnt_ret[sva_v_free_entry][sva_v_iss_cnt[sva_v_free_entry]]
                      <= issued_count;
                  end
                if(sva_v_ret_entry && !sva_v_ret_rst_entry)
                  if(sva_v_cnt_ret[sva_v_ret_entry][sva_v_ret_cnt[sva_v_ret_entry]] == 1)
                  begin
                    sva_v_ret_cnt[sva_v_ret_entry] <= sva_v_ret_cnt[sva_v_ret_entry]+1;
                  end
                  else begin
                    sva_v_cnt_ret[sva_v_ret_entry][sva_v_ret_cnt[sva_v_ret_entry]]
                      <= sva_v_cnt_ret[sva_v_ret_entry][sva_v_ret_cnt[sva_v_ret_entry]] - 1;
                  end
              end

           endcase
         end
       end // always
       always @* begin
          if(sva_v_ret_entry) begin
             sva_v_queue_head =
               sva_v_queue[sva_v_ret_entry][sva_v_ret_cnt[sva_v_ret_entry]];
             sva_v_valid_simultaneous_iss_ret =
               sva_v_valid_arr[sva_v_ret_entry] ||
               issued && (issued_id == returned_id) && (min_cks == 0);
             sva_v_empty = !sva_v_valid_arr[sva_v_ret_entry];
          end
          else begin
             sva_v_queue_head = 1'b1;
             sva_v_valid_simultaneous_iss_ret = 1'b1;
             sva_v_empty = 1'b1;
          end
       end

       function [latency_bw+1:0] latency
         (
          input [latency_bw:0] current,
          input [latency_bw:0] previous
          );
         latency = (current >= previous) ?
                {1'b0, (current - previous)} :
                ({1'b1, current} - {1'b0, previous});
       endfunction // latency

       assign sva_v_delay = latency(sva_v_clock_count ,sva_v_queue_head);

       generate
         for ( i=1; i<=max_id_instances; i=i+1) begin : loop_max_cksency_ok
           assign sva_v_max_cksency_ok[i] = sva_v_valid_arr[i] &&
                 (latency(sva_v_clock_count,
                         sva_v_queue[i][sva_v_ret_cnt[i]]) <= max_cks);
         end : loop_max_cksency_ok
       endgenerate

`endif // OVL_SHARED_CODE

`ifdef OVL_ASSERT_ON

           property OVL_VALID_ID_MIN_LAT_P;
               @( posedge clk) disable iff (`OVL_RESET_SIGNAL!=1'b1)
                 (returned &&  !(flush && (sva_v_rst_entry == sva_v_ret_entry))&&
                ( (sva_v_ret_entry != 0) && (!sva_v_block_lat_chk[sva_v_ret_entry])
                 || (returned && issued && sva_v_iss_returned_id && ( sva_v_current_out < max_instances_per_id ) )) |->
                     ( issued && returned && sva_v_iss_returned_id && ( sva_v_current_out < max_instances_per_id ) ) ? (min_cks==0) :
                 (sva_v_valid_arr[sva_v_ret_entry]) ?
                     (sva_v_delay >= min_cks)
                     :
                     (min_cks == 0));

           endproperty : OVL_VALID_ID_MIN_LAT_P

           property OVL_VALID_ID_ISSUED_ID_OK_P;
             @( posedge clk) disable iff (`OVL_RESET_SIGNAL!=1'b1)
               (sva_v_issued_entry != 0) && issued &&
           !(flush && (sva_v_issued_entry == sva_v_rst_entry)) &&
           !((min_cks == 0) && returned &&
             (sva_v_ret_entry == sva_v_issued_entry)) &&
            !((sva_v_issued_arr[sva_v_ret_entry] > 0 ) && returned && issued && (issued_id == returned_id))
                |->
                 ( sva_v_current_out < max_instances_per_id );
           endproperty : OVL_VALID_ID_ISSUED_ID_OK_P

           property OVL_VALID_ID_RET_ID_OK_P;
             @( posedge clk ) disable iff (`OVL_RESET_SIGNAL!=1'b1)
               sva_v_ret &&
              ! (issued && ( issued_id == returned_id ) && (sva_v_current_out < max_instances_per_id) && (sva_v_outstanding_ids <= max_ids)) |->
                 ( sva_v_ret_entry != 0 );
           endproperty : OVL_VALID_ID_RET_ID_OK_P

           property OVL_VALID_IDS_MAX_ISSUED_IDS_OK_P;
             @( posedge clk ) disable iff (`OVL_RESET_SIGNAL!=1'b1)
               ( sva_v_issued &&
                 !(flush && (sva_v_rst_entry != 0)) &&
                 !(returned && (sva_v_ret_entry != 0) &&
                  (sva_v_current_out == 1)) &&
                 (sva_v_issued_entry == 0)  &&
                 !((sva_v_issued_arr[sva_v_ret_entry] == 1) && (sva_v_ret_entry > 0) && returned && (sva_v_outstanding_ids <= max_ids))
               ) |->
                   (sva_v_free_entry != 0) &&
                   (sva_v_outstanding_ids < max_ids);
           endproperty : OVL_VALID_IDS_MAX_ISSUED_IDS_OK_P

          property OVL_VALID_ID_NB_RET_PER_ISSUED_0_P;
            @(posedge clk)  disable iff (`OVL_RESET_SIGNAL!=1'b1)
              ( issued |-> issued_count > 0);
          endproperty : OVL_VALID_ID_NB_RET_PER_ISSUED_0_P

  `ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

    property OVL_VALID_ID_XZ_ISSUED_ID_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    ((issued ==1'b1)|->!($isunknown(issued_id)) );
    endproperty

    property OVL_VALID_ID_XZ_RET_ID_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    ((returned ==1'b1)|->!($isunknown(returned_id)) );
    endproperty

    property OVL_VALID_ID_XZ_ISSUED_SIG_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(issued)));
    endproperty

    property OVL_VALID_ID_XZ_RET_SIG_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(returned)));
    endproperty

    property OVL_VALID_ID_XZ_RESET_SIG_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(flush)));
    endproperty

    property OVL_VALID_ID_XZ_RESET_ID_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    ((flush ==1'b1)|->!($isunknown(flush_id)) );
    endproperty

 `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

 generate
    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert

      for ( i=1; i<=max_id_instances; i=i+1) begin : loop_max_cksency
        property OVL_VALID_ID_MAX_LAT_P;
          @(posedge clk) disable iff (`OVL_RESET_SIGNAL!=1'b1)
            sva_v_valid_arr[i] && !sva_v_block_lat_chk[i]
                |-> !($fell(sva_v_max_cksency_ok[i]));
        endproperty :OVL_VALID_ID_MAX_LAT_P
        assert property(OVL_VALID_ID_MAX_LAT_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"OVL_VALID_ID_MAX_LAT check violated");
            error_event = 1;
          end
      end : loop_max_cksency

      A_OVL_VALID_ID_MIN_LAT_P:
          assert property (OVL_VALID_ID_MIN_LAT_P)
          else
            begin
              ovl_error_t(`OVL_FIRE_2STATE,"OVL_VALID_ID_MIN_LAT check violated");
              error_event = 1;
            end
      A_VALID_ID_ISSUED_ID_OK_P:
          assert property (OVL_VALID_ID_ISSUED_ID_OK_P)
          else
            begin
              ovl_error_t(`OVL_FIRE_2STATE,"OVL_VALID_ID_ISSUED_ID_OK check violated");
              error_event = 1;
            end
      A_VALID_ID_RET_ID_OK_P:
          assert property (OVL_VALID_ID_RET_ID_OK_P)
          else
            begin
              ovl_error_t(`OVL_FIRE_2STATE,"OVL_VALID_ID_RET_ID_OK check violated");
              error_event = 1;
            end
      A_VALID_IDS_MAX_ISSUED_IDS_OK_P:
          assert property (OVL_VALID_IDS_MAX_ISSUED_IDS_OK_P)
          else
            begin
              ovl_error_t(`OVL_FIRE_2STATE,"OVL_VALID_IDS_MAX_ISSUED_IDS_OK check violated");
              error_event = 1;
            end
      A_VALID_ID_NB_RET_PER_ISSUED_0_P:
          assert property (OVL_VALID_ID_NB_RET_PER_ISSUED_0_P)
          else
            begin
              ovl_error_t(`OVL_FIRE_2STATE,"OVL_VALID_ID_NB_RET_PER_ISSUED_0_P check violated");
              error_event = 1;
            end

       `ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

        A_OVL_VALID_ID_XZ_ISSUED_ID_P:
        assert property (OVL_VALID_ID_XZ_ISSUED_ID_P)
        else
        begin
          ovl_error_t(`OVL_FIRE_XCHECK,"issued_id contains X or Z when issued is asserted");
          error_event_xz = 1;
        end
        A_OVL_VALID_ID_XZ_RET_ID_P:
        assert property (OVL_VALID_ID_XZ_RET_ID_P)
        else
        begin
          ovl_error_t(`OVL_FIRE_XCHECK,"returned_id contains X or Z when returned is asserted");
          error_event_xz = 1;
        end

        A_OVL_VALID_ID_XZ_ISSUED_SIG_P:
        assert property (OVL_VALID_ID_XZ_ISSUED_SIG_P)
        else
        begin
          ovl_error_t(`OVL_FIRE_XCHECK,"issued contains X or Z");
          error_event_xz = 1;
        end

        A_OVL_VALID_ID_XZ_RET_SIG_P:
        assert property (OVL_VALID_ID_XZ_RET_SIG_P)
        else
        begin
          ovl_error_t(`OVL_FIRE_XCHECK,"returned contains X or Z");
          error_event_xz = 1;
        end

        A_OVL_VALID_ID_XZ_RESET_ID_P:
        assert property (OVL_VALID_ID_XZ_RESET_ID_P)
        else
        begin
          ovl_error_t(`OVL_FIRE_XCHECK,"flush_id contains X or Z when flush is asserted");
          error_event_xz = 1;
        end

        A_OVL_VALID_ID_XZ_RESET_SIG_P:
        assert property (OVL_VALID_ID_XZ_RESET_SIG_P)
        else
        begin
          ovl_error_t(`OVL_FIRE_XCHECK,"flush contains X or Z");
          error_event_xz = 1;
        end

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end

  `OVL_ASSUME_2STATE,
  `OVL_ASSUME: begin : ovl_assume

     for ( i=1; i<=max_id_instances; i=i+1) begin : loop_max_cksency
               property OVL_VALID_ID_MAX_LAT_P;
                  @(posedge clk) disable iff (`OVL_RESET_SIGNAL!=1'b1)
                    sva_v_valid_arr[i] && !sva_v_block_lat_chk[i]
                                       |-> !($fell(sva_v_max_cksency_ok[i]));
               endproperty :OVL_VALID_ID_MAX_LAT_P
             assume property(OVL_VALID_ID_MAX_LAT_P);
             end : loop_max_cksency

      M_OVL_VALID_ID_MIN_LAT_P:
          assume property (OVL_VALID_ID_MIN_LAT_P);

      M_VALID_ID_ISSUED_ID_OK_P:
          assume property (OVL_VALID_ID_ISSUED_ID_OK_P);

      M_VALID_ID_RET_ID_OK_P:
          assume property (OVL_VALID_ID_RET_ID_OK_P);

      M_VALID_IDS_MAX_ISSUED_IDS_OK_P:
          assume property (OVL_VALID_IDS_MAX_ISSUED_IDS_OK_P);

      M_VALID_ID_NB_RET_PER_ISSUED_0_P:
          assume property (OVL_VALID_ID_NB_RET_PER_ISSUED_0_P);

       `ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

        M_OVL_VALID_ID_XZ_ISSUED_ID_P:
        assume property (OVL_VALID_ID_XZ_ISSUED_ID_P);

        M_OVL_VALID_ID_XZ_RET_ID_P:
        assume property (OVL_VALID_ID_XZ_RET_ID_P);

        M_OVL_VALID_ID_XZ_ISSUED_SIG_P:
        assume property (OVL_VALID_ID_XZ_ISSUED_SIG_P);

        M_OVL_VALID_ID_XZ_RET_SIG_P:
        assume property (OVL_VALID_ID_XZ_RET_SIG_P);

        M_OVL_VALID_ID_XZ_RESET_ID_P:
        assume property (OVL_VALID_ID_XZ_RESET_ID_P);

        M_OVL_VALID_ID_XZ_RESET_SIG_P:
        assume property (OVL_VALID_ID_XZ_RESET_SIG_P);

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF
      end

  `OVL_IGNORE : begin :ovl_ignore
            //do nothing
             end
      default     : initial ovl_error_t(`OVL_FIRE_2STATE,"");
    endcase
  endgenerate

`endif // OVL_ASSERT_ON

`ifdef OVL_COVER_ON

`ifdef OVL_COVERGROUP_ON

      covergroup latency_cg @(posedge clk);
         coverpoint int'(sva_v_delay)
           iff( `OVL_RESET_SIGNAL &&
               returned && !sva_v_empty) {
             bins observed_latency_good[] = {[min_cks:max_cks]};
             bins observed_latency_bad = default;}
         option.per_instance = 1;
         option.at_least = 1;
         option.name = "observed_latency";
         option.comment = "Bin index is the observed latency value";
       endgroup : latency_cg

     covergroup outstanding_ids_cg @(posedge clk);
         coverpoint int'(sva_v_outstanding_ids)
           iff( `OVL_RESET_SIGNAL &&
              ( returned || issued) && !sva_v_empty) {
             bins observed_outstanding_ids[] = {[0:max_id_instances]};
         }
         option.per_instance = 1;
         option.at_least = 1;
         option.name = "outstanding_ids";
         option.comment = "Bin index is the number of outstanding ids";
       endgroup : outstanding_ids_cg

`endif // `ifdef OVL_COVERGROUP_ON

  generate

    if (coverage_level != `OVL_COVER_NONE) begin : ovl_cover
     if (OVL_COVER_SANITY_ON) begin : ovl_cover_sanity

      cover_issued_asserted:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                     issued ) )
                       ovl_cover_t("Issued sig asserted");

      cover_returned_asserted:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                     returned ) )
                       ovl_cover_t("Ret sig asserted");

      cover_flush_asserted:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                     flush ) )
                       ovl_cover_t("reset sig asserted");

     end //sanity coverage

     if (OVL_COVER_CORNER_ON) begin : ovl_cover_corner

       cover_returned_with_exact_min_cks:
              cover property(
                @ ( posedge clk)
                     `OVL_RESET_SIGNAL &&
                    returned && !sva_v_empty &&
                      sva_v_delay == min_cks
              )
              ovl_cover_t("ID returned in min_cks cycles");


       cover_returned_with_exact_max_cks:
              cover property(
                @ ( posedge clk)
                     `OVL_RESET_SIGNAL &&
                       returned && !sva_v_empty &&
                         sva_v_delay == max_cks
                  )
              ovl_cover_t("ID returned in max_cks cycles");

      cover_issued_ids_reached_max_ids:
              cover property(
                @ ( posedge clk)
                    `OVL_RESET_SIGNAL &&
                      ( sva_v_issued &&
                        !(flush && (sva_v_rst_entry != 0)) &&
                        !(returned && (sva_v_ret_entry != 0) &&
                          (sva_v_current_out == 1)) &&
                        (sva_v_issued_entry == 0)
                      ) &&
                      ((sva_v_outstanding_ids == max_id_instances - 1) ||
                       (sva_v_outstanding_ids == max_ids - 1) ) )
              ovl_cover_t("Number of outstanding IDs is max_ids");

       cover_issued_id_reached_max_instances_per_id:
              cover property(
                @ ( posedge clk)
                    `OVL_RESET_SIGNAL && issued &&
                      !(returned && sva_v_iss_returned_id && (min_cks == 0)) &&
                      ((sva_v_issued_entry) ?
                         !(flush && sva_v_iss_rst_id) &&
                         (sva_v_current_out == max_instances_per_id-1)
                         :
                         (sva_v_free_entry && (max_instances_per_id == 1))
                       )
                    )
               ovl_cover_t("Number of outstanding instances of an ID is max_instances_per_id");

     end //Corner case Coverage


    if (OVL_COVER_BASIC_ON) begin : ovl_cover_basic

`ifdef OVL_COVERGROUP_ON

         latency_cg lateny_cover = new();
         outstanding_ids_cg outstanding_ids_cover = new();

`endif // `ifdef OVL_COVERGROUP_ON

     end : ovl_cover_basic

  end:ovl_cover

  endgenerate

`endif
