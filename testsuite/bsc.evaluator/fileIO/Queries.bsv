String rd_fname = "sysBasicRead.txt";
String wr_fname = "sysQueries.log";

(* synthesize *)
module sysQueries ();
   Bool b;

   Handle rd_hdl <- openFile(rd_fname, ReadMode);

   b <- hIsOpen(rd_hdl);
   if (!b) error("rd_fname not open");
   b <- hIsClosed(rd_hdl);
   if (b) error("rd_fname closed");
   b <- hIsReadable(rd_hdl);
   if (!b) error("rd_fname not readable");
   b <- hIsWritable(rd_hdl);
   if (b) error("rd_fname writable");

   hClose(rd_hdl);

   b <- hIsOpen(rd_hdl);
   if (b) error("rd_fname open");
   b <- hIsClosed(rd_hdl);
   if (!b) error("rd_fname not closed");

   Handle wr_hdl <- openFile(wr_fname, WriteMode);

   b <- hIsOpen(wr_hdl);
   if (!b) error("wr_fname not open");
   b <- hIsClosed(wr_hdl);
   if (b) error("wr_fname closed");
   b <- hIsReadable(wr_hdl);
   if (b) error("wr_fname readable");
   b <- hIsWritable(wr_hdl);
   if (!b) error("wr_fname not writable");

   hClose(wr_hdl);

   b <- hIsOpen(wr_hdl);
   if (b) error("wr_fname open");
   b <- hIsClosed(wr_hdl);
   if (!b) error("wr_fname not closed");

   Handle ap_hdl <- openFile(wr_fname, AppendMode);

   b <- hIsOpen(ap_hdl);
   if (!b) error("wr_fname not open");
   b <- hIsClosed(ap_hdl);
   if (b) error("wr_fname closed");
   b <- hIsReadable(ap_hdl);
   if (b) error("wr_fname readable");
   b <- hIsWritable(ap_hdl);
   if (!b) error("wr_fname not writable");

   hClose(ap_hdl);

   b <- hIsOpen(ap_hdl);
   if (b) error("wr_fname open");
   b <- hIsClosed(ap_hdl);
   if (!b) error("wr_fname not closed");

endmodule

