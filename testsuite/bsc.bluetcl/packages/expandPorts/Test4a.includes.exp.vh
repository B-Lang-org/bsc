// autocreated by expandPorts.tcl 2.0 and portUtil.tcl 2.0

  wire   CLK;
  wire   RST_N;
  // ====================
  // Method = method4
  //   ready  => RDY_method4            1   Bit#(1)
  //   enable => EN_method4             1   Bit#(1)
  //   result => method4              216   {ActionValue#(Vector::Vector#(3, Vector::Vector#(4, Test4a::TS)))}
  //   input  => method4_in1           32   Int#(32)
  wire   RDY_method4;
  wire   EN_method4;
  wire   [ 215 : 0 ] method4;
  wire   [ 2 : 0 ] method4_0_0_a;  // method4[215:213]
  wire   [ 3 : 0 ] method4_0_0_b;  // method4[212:209]
  wire   [ 2 : 0 ] method4_0_0_c_x;  // method4[208:206]
  wire   [ 3 : 0 ] method4_0_0_c_y;  // method4[205:202]
  wire   [ 3 : 0 ] method4_0_0_c_z;  // method4[201:198]
  wire   [ 2 : 0 ] method4_0_1_a;  // method4[197:195]
  wire   [ 3 : 0 ] method4_0_1_b;  // method4[194:191]
  wire   [ 2 : 0 ] method4_0_1_c_x;  // method4[190:188]
  wire   [ 3 : 0 ] method4_0_1_c_y;  // method4[187:184]
  wire   [ 3 : 0 ] method4_0_1_c_z;  // method4[183:180]
  wire   [ 2 : 0 ] method4_0_2_a;  // method4[179:177]
  wire   [ 3 : 0 ] method4_0_2_b;  // method4[176:173]
  wire   [ 2 : 0 ] method4_0_2_c_x;  // method4[172:170]
  wire   [ 3 : 0 ] method4_0_2_c_y;  // method4[169:166]
  wire   [ 3 : 0 ] method4_0_2_c_z;  // method4[165:162]
  wire   [ 2 : 0 ] method4_0_3_a;  // method4[161:159]
  wire   [ 3 : 0 ] method4_0_3_b;  // method4[158:155]
  wire   [ 2 : 0 ] method4_0_3_c_x;  // method4[154:152]
  wire   [ 3 : 0 ] method4_0_3_c_y;  // method4[151:148]
  wire   [ 3 : 0 ] method4_0_3_c_z;  // method4[147:144]
  wire   [ 2 : 0 ] method4_1_0_a;  // method4[143:141]
  wire   [ 3 : 0 ] method4_1_0_b;  // method4[140:137]
  wire   [ 2 : 0 ] method4_1_0_c_x;  // method4[136:134]
  wire   [ 3 : 0 ] method4_1_0_c_y;  // method4[133:130]
  wire   [ 3 : 0 ] method4_1_0_c_z;  // method4[129:126]
  wire   [ 2 : 0 ] method4_1_1_a;  // method4[125:123]
  wire   [ 3 : 0 ] method4_1_1_b;  // method4[122:119]
  wire   [ 2 : 0 ] method4_1_1_c_x;  // method4[118:116]
  wire   [ 3 : 0 ] method4_1_1_c_y;  // method4[115:112]
  wire   [ 3 : 0 ] method4_1_1_c_z;  // method4[111:108]
  wire   [ 2 : 0 ] method4_1_2_a;  // method4[107:105]
  wire   [ 3 : 0 ] method4_1_2_b;  // method4[104:101]
  wire   [ 2 : 0 ] method4_1_2_c_x;  // method4[100:98]
  wire   [ 3 : 0 ] method4_1_2_c_y;  // method4[97:94]
  wire   [ 3 : 0 ] method4_1_2_c_z;  // method4[93:90]
  wire   [ 2 : 0 ] method4_1_3_a;  // method4[89:87]
  wire   [ 3 : 0 ] method4_1_3_b;  // method4[86:83]
  wire   [ 2 : 0 ] method4_1_3_c_x;  // method4[82:80]
  wire   [ 3 : 0 ] method4_1_3_c_y;  // method4[79:76]
  wire   [ 3 : 0 ] method4_1_3_c_z;  // method4[75:72]
  wire   [ 2 : 0 ] method4_2_0_a;  // method4[71:69]
  wire   [ 3 : 0 ] method4_2_0_b;  // method4[68:65]
  wire   [ 2 : 0 ] method4_2_0_c_x;  // method4[64:62]
  wire   [ 3 : 0 ] method4_2_0_c_y;  // method4[61:58]
  wire   [ 3 : 0 ] method4_2_0_c_z;  // method4[57:54]
  wire   [ 2 : 0 ] method4_2_1_a;  // method4[53:51]
  wire   [ 3 : 0 ] method4_2_1_b;  // method4[50:47]
  wire   [ 2 : 0 ] method4_2_1_c_x;  // method4[46:44]
  wire   [ 3 : 0 ] method4_2_1_c_y;  // method4[43:40]
  wire   [ 3 : 0 ] method4_2_1_c_z;  // method4[39:36]
  wire   [ 2 : 0 ] method4_2_2_a;  // method4[35:33]
  wire   [ 3 : 0 ] method4_2_2_b;  // method4[32:29]
  wire   [ 2 : 0 ] method4_2_2_c_x;  // method4[28:26]
  wire   [ 3 : 0 ] method4_2_2_c_y;  // method4[25:22]
  wire   [ 3 : 0 ] method4_2_2_c_z;  // method4[21:18]
  wire   [ 2 : 0 ] method4_2_3_a;  // method4[17:15]
  wire   [ 3 : 0 ] method4_2_3_b;  // method4[14:11]
  wire   [ 2 : 0 ] method4_2_3_c_x;  // method4[10:8]
  wire   [ 3 : 0 ] method4_2_3_c_y;  // method4[7:4]
  wire   [ 3 : 0 ] method4_2_3_c_z;  // method4[3:0]
  wire   [ 31 : 0 ] method4_in1;


`ifndef __EXPANDPORTS_NO_RENAMES__
  assign method4_0_0_a = method4[215:213];
  assign method4_0_0_b = method4[212:209];
  assign method4_0_0_c_x = method4[208:206];
  assign method4_0_0_c_y = method4[205:202];
  assign method4_0_0_c_z = method4[201:198];
  assign method4_0_1_a = method4[197:195];
  assign method4_0_1_b = method4[194:191];
  assign method4_0_1_c_x = method4[190:188];
  assign method4_0_1_c_y = method4[187:184];
  assign method4_0_1_c_z = method4[183:180];
  assign method4_0_2_a = method4[179:177];
  assign method4_0_2_b = method4[176:173];
  assign method4_0_2_c_x = method4[172:170];
  assign method4_0_2_c_y = method4[169:166];
  assign method4_0_2_c_z = method4[165:162];
  assign method4_0_3_a = method4[161:159];
  assign method4_0_3_b = method4[158:155];
  assign method4_0_3_c_x = method4[154:152];
  assign method4_0_3_c_y = method4[151:148];
  assign method4_0_3_c_z = method4[147:144];
  assign method4_1_0_a = method4[143:141];
  assign method4_1_0_b = method4[140:137];
  assign method4_1_0_c_x = method4[136:134];
  assign method4_1_0_c_y = method4[133:130];
  assign method4_1_0_c_z = method4[129:126];
  assign method4_1_1_a = method4[125:123];
  assign method4_1_1_b = method4[122:119];
  assign method4_1_1_c_x = method4[118:116];
  assign method4_1_1_c_y = method4[115:112];
  assign method4_1_1_c_z = method4[111:108];
  assign method4_1_2_a = method4[107:105];
  assign method4_1_2_b = method4[104:101];
  assign method4_1_2_c_x = method4[100:98];
  assign method4_1_2_c_y = method4[97:94];
  assign method4_1_2_c_z = method4[93:90];
  assign method4_1_3_a = method4[89:87];
  assign method4_1_3_b = method4[86:83];
  assign method4_1_3_c_x = method4[82:80];
  assign method4_1_3_c_y = method4[79:76];
  assign method4_1_3_c_z = method4[75:72];
  assign method4_2_0_a = method4[71:69];
  assign method4_2_0_b = method4[68:65];
  assign method4_2_0_c_x = method4[64:62];
  assign method4_2_0_c_y = method4[61:58];
  assign method4_2_0_c_z = method4[57:54];
  assign method4_2_1_a = method4[53:51];
  assign method4_2_1_b = method4[50:47];
  assign method4_2_1_c_x = method4[46:44];
  assign method4_2_1_c_y = method4[43:40];
  assign method4_2_1_c_z = method4[39:36];
  assign method4_2_2_a = method4[35:33];
  assign method4_2_2_b = method4[32:29];
  assign method4_2_2_c_x = method4[28:26];
  assign method4_2_2_c_y = method4[25:22];
  assign method4_2_2_c_z = method4[21:18];
  assign method4_2_3_a = method4[17:15];
  assign method4_2_3_b = method4[14:11];
  assign method4_2_3_c_x = method4[10:8];
  assign method4_2_3_c_y = method4[7:4];
  assign method4_2_3_c_z = method4[3:0];
`endif

`ifndef __EXPANDPORTS_DONT_CREATE_DUT__
  mkTest4a _mkTest4a ( 
   .CLK( CLK ),
   .RST_N( RST_N ),
   .RDY_method4( RDY_method4 ),
   .EN_method4( EN_method4 ),
   .method4( method4 ),
   .method4_in1( method4_in1 )
  );
`endif
