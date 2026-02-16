
import Vector :: * ;
import StmtFSM :: * ;

// Test fromChunks function with various chunk sizes and types

(* synthesize *)
module sysFromChunksTest();

   Stmt testseq =
   seq
      $display("=== fromChunks Tests ===");
      $display("");

      // Test 1: Basic 8-bit chunks to 32-bit value
      action
         Vector#(4, Bit#(8)) chunks8 = cons(8'h12, cons(8'h34, cons(8'h56, cons(8'h78, nil))));
         Bit#(32) result32 = fromChunks(chunks8);
         $display("Test 1: 8-bit chunks to 32-bit");
         $display("  Chunks: %h %h %h %h", chunks8[0], chunks8[1], chunks8[2], chunks8[3]);
         $display("  Result: %h (expected: 12345678)", result32);
      endaction

      // Test 2: 16-bit chunks to 64-bit value
      action
         Vector#(4, Bit#(16)) chunks16 = cons(16'hABCD, cons(16'hEF01, cons(16'h2345, cons(16'h6789, nil))));
         Bit#(64) result64 = fromChunks(chunks16);
         $display("Test 2: 16-bit chunks to 64-bit");
         $display("  Chunks: %h %h %h %h", chunks16[0], chunks16[1], chunks16[2], chunks16[3]);
         $display("  Result: %h (expected: ABCDEF0123456789)", result64);
      endaction

      // Test 3: Round-trip test (toChunks -> fromChunks)
      action
         Bit#(48) original = 48'hDEADBEEFFEED;
         Vector#(6, Bit#(8)) chunks = toChunks(original);
         Bit#(48) recovered = fromChunks(chunks);
         $display("Test 3: Round-trip 48-bit value");
         $display("  Original:  %h", original);
         $display("  Chunks: %h %h %h %h %h %h",
                  chunks[0], chunks[1], chunks[2], chunks[3], chunks[4], chunks[5]);
         $display("  Recovered: %h", recovered);
         $display("  Match: %s", (original == recovered) ? "PASS" : "FAIL");
      endaction

      // Test 4: UInt type conversion
      action
         Vector#(4, Bit#(8)) chunks_uint = cons(8'h01, cons(8'h02, cons(8'h03, cons(8'h04, nil))));
         UInt#(32) result_uint = fromChunks(chunks_uint);
         $display("Test 4: 8-bit chunks to UInt#(32)");
         $display("  Chunks: %h %h %h %h", chunks_uint[0], chunks_uint[1],
                  chunks_uint[2], chunks_uint[3]);
         $display("  Result: %h (expected: 01020304)", result_uint);
      endaction

      // Test 5: Int type conversion
      action
         Vector#(2, Bit#(16)) chunks_int = cons(16'hFFFF, cons(16'h8000, nil));
         Int#(32) result_int = fromChunks(chunks_int);
         $display("Test 5: 16-bit chunks to Int#(32)");
         $display("  Chunks: %h %h", chunks_int[0], chunks_int[1]);
         $display("  Result: %h (expected: FFFF8000)", result_int);
         $display("  As signed: %0d", result_int);
      endaction

      // Test 6: Single chunk (identity case)
      action
         Vector#(1, Bit#(32)) single_chunk = cons(32'h87654321, nil);
         Bit#(32) result_single = fromChunks(single_chunk);
         $display("Test 6: Single chunk identity");
         $display("  Chunk:  %h", single_chunk[0]);
         $display("  Result: %h", result_single);
         $display("  Match: %s", (single_chunk[0] == result_single) ? "PASS" : "FAIL");
      endaction

      // Test 7: Small value with padding in last chunk
      action
         Vector#(2, Bit#(8)) chunks_small = cons(8'h5A, cons(8'hA5, nil));
         Bit#(12) result_12 = fromChunks(chunks_small);
         $display("Test 7: 12-bit value from 8-bit chunks (with padding)");
         $display("  Chunks: %h %h", chunks_small[0], chunks_small[1]);
         $display("  Result: %h (expected: 5A5, padding dropped)", result_12);
      endaction

      // Test 8: Round-trip with various sizes
      action
         Bit#(20) val20 = 20'hABCDE;
         Vector#(3, Bit#(8)) chunks20 = toChunks(val20);
         Bit#(20) recovered20 = fromChunks(chunks20);
         $display("Test 8: Round-trip 20-bit value");
         $display("  Original:  %h", val20);
         $display("  Recovered: %h", recovered20);
         $display("  Match: %s", (val20 == recovered20) ? "PASS" : "FAIL");
      endaction

      // Test 9: Large 128-bit value
      action
         Bit#(128) val128 = 128'h0123456789ABCDEF_FEDCBA9876543210;
         Vector#(16, Bit#(8)) chunks128 = toChunks(val128);
         Bit#(128) recovered128 = fromChunks(chunks128);
         $display("Test 9: Round-trip 128-bit value");
         $display("  Original:  %h", val128);
         $display("  Recovered: %h", recovered128);
         $display("  Match: %s", (val128 == recovered128) ? "PASS" : "FAIL");
      endaction

      // Test 10: 4-bit chunks to 16-bit value
      action
         Vector#(4, Bit#(4)) chunks4 = cons(4'h1, cons(4'h2, cons(4'h3, cons(4'h4, nil))));
         Bit#(16) result16 = fromChunks(chunks4);
         $display("Test 10: 4-bit chunks to 16-bit");
         $display("  Chunks: %h %h %h %h", chunks4[0], chunks4[1], chunks4[2], chunks4[3]);
         $display("  Result: %h (expected: 1234)", result16);
      endaction

      $display("");
      $display("=== Non-even chunk size tests ===");
      $display("");

      // Test 11: 7-bit value from 5-bit chunks (padding in last chunk)
      action
         Vector#(2, Bit#(5)) chunks5_to_7 = cons(5'h1F, cons(5'h03, nil));
         Bit#(7) result7 = fromChunks(chunks5_to_7);
         $display("Test 11: 7-bit value from 5-bit chunks");
         $display("  Chunks: %b %b", chunks5_to_7[0], chunks5_to_7[1]);
         $display("  Result: %b (expected: 1111111, 7 bits from 10 bits)", result7);
      endaction

      // Test 12: 13-bit value from 5-bit chunks
      action
         Vector#(3, Bit#(5)) chunks5_to_13 = cons(5'h1F, cons(5'h15, cons(5'h0A, nil)));
         Bit#(13) result13 = fromChunks(chunks5_to_13);
         $display("Test 12: 13-bit value from 5-bit chunks");
         $display("  Chunks: %b %b %b", chunks5_to_13[0], chunks5_to_13[1], chunks5_to_13[2]);
         $display("  Result: %b (13 bits from 15 bits)", result13);
         $display("  Result hex: %h", result13);
      endaction

      // Test 13: 10-bit value from 3-bit chunks (needs 4 chunks, last has padding)
      action
         Vector#(4, Bit#(3)) chunks3_to_10 = cons(3'h7, cons(3'h6, cons(3'h5, cons(3'h4, nil))));
         Bit#(10) result10 = fromChunks(chunks3_to_10);
         $display("Test 13: 10-bit value from 3-bit chunks");
         $display("  Chunks: %b %b %b %b", chunks3_to_10[0], chunks3_to_10[1], chunks3_to_10[2], chunks3_to_10[3]);
         $display("  Result: %b (10 bits from 12 bits)", result10);
         $display("  Result hex: %h", result10);
      endaction

      // Test 14: Round-trip with non-even sizes (17-bit value, 5-bit chunks)
      action
         Bit#(17) val17 = 17'h1CAFE;
         Vector#(4, Bit#(5)) chunks17 = toChunks(val17);
         Bit#(17) recovered17 = fromChunks(chunks17);
         $display("Test 14: Round-trip 17-bit value with 5-bit chunks");
         $display("  Original:  %h (%b)", val17, val17);
         $display("  Chunks: %b %b %b %b", chunks17[0], chunks17[1], chunks17[2], chunks17[3]);
         $display("  Recovered: %h (%b)", recovered17, recovered17);
         $display("  Match: %s", (val17 == recovered17) ? "PASS" : "FAIL");
      endaction

      // Test 15: 23-bit value from 7-bit chunks (needs 4 chunks, last has 2 bits padding)
      action
         Bit#(23) val23 = 23'h7FFFFF;
         Vector#(4, Bit#(7)) chunks23 = toChunks(val23);
         Bit#(23) recovered23 = fromChunks(chunks23);
         $display("Test 15: Round-trip 23-bit value with 7-bit chunks");
         $display("  Original:  %h", val23);
         $display("  Chunks: %b %b %b %b", chunks23[0], chunks23[1], chunks23[2], chunks23[3]);
         $display("  Recovered: %h", recovered23);
         $display("  Match: %s", (val23 == recovered23) ? "PASS" : "FAIL");
      endaction

      // Test 16: 11-bit value from 6-bit chunks
      action
         Bit#(11) val11 = 11'h7FF;
         Vector#(2, Bit#(6)) chunks11 = toChunks(val11);
         Bit#(11) recovered11 = fromChunks(chunks11);
         $display("Test 16: Round-trip 11-bit value with 6-bit chunks");
         $display("  Original:  %h (%b)", val11, val11);
         $display("  Chunks: %b %b", chunks11[0], chunks11[1]);
         $display("  Recovered: %h (%b)", recovered11, recovered11);
         $display("  Match: %s", (val11 == recovered11) ? "PASS" : "FAIL");
      endaction

      // Test 17: 31-bit value from 9-bit chunks (needs 4 chunks, last has 4 bits padding)
      action
         Bit#(31) val31 = 31'h5A5A5A5A;
         Vector#(4, Bit#(9)) chunks31 = toChunks(val31);
         Bit#(31) recovered31 = fromChunks(chunks31);
         $display("Test 17: Round-trip 31-bit value with 9-bit chunks");
         $display("  Original:  %h", val31);
         $display("  Recovered: %h", recovered31);
         $display("  Match: %s", (val31 == recovered31) ? "PASS" : "FAIL");
      endaction

      $display("");
      $display("=== All fromChunks tests completed ===");
   endseq;

   mkAutoFSM(testseq);

endmodule
