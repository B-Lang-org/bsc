// autocreated by expandPorts.tcl 2.0 and portUtil.tcl 2.0

  wire   CLK;
  wire   RST_N;
  // ====================
  // Method = method1
  //   ready  => RDY_method1            1   Bit#(1)
  //   enable => EN_method1             1   Bit#(1)
  //   input  => method1_in1           32   Int#(32)
  //   input  => method1_in2           32   Int#(32)
  wire   RDY_method1;
  wire   EN_method1;
  wire   [ 31 : 0 ] method1_in1;
  wire   [ 31 : 0 ] method1_in2;

  // ====================
  // Method = method2
  //   ready  => RDY_method2            1   Bit#(1)
  //   result => method2               32   Int#(32)
  //   input  => method2_in1           32   Int#(32)
  //   input  => method2_in2           32   Int#(32)
  wire   RDY_method2;
  wire   [ 31 : 0 ] method2;
  wire   [ 31 : 0 ] method2_in1;
  wire   [ 31 : 0 ] method2_in2;

  // ====================
  // Method = method3
  //   ready  => RDY_method3            1   Bit#(1)
  //   result => method3               32   Int#(32)
  wire   RDY_method3;
  wire   [ 31 : 0 ] method3;

  // ====================
  // Method = method4
  //   ready  => RDY_method4            1   Bit#(1)
  //   enable => EN_method4             1   Bit#(1)
  //   result => method4              216   {ActionValue#(Vector::Vector#(3, Vector::Vector#(4, Test4::TS)))}
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

  // ====================
  // Method = method5
  //   ready  => RDY_method5            1   Bit#(1)
  //   enable => EN_method5             1   Bit#(1)
  //   input  => method5_in1            4   Bit#(4)
  wire   RDY_method5;
  wire   EN_method5;
  wire   [ 3 : 0 ] method5_in1;

  // ====================
  // Method = method6
  //   ready  => RDY_method6            1   Bit#(1)
  //   result => method6               32   Int#(32)
  //   input  => method6_in1           18   Test4::TS
  wire   RDY_method6;
  wire   [ 31 : 0 ] method6;
  wire   [ 17 : 0 ] method6_in1;
  wire   [ 2 : 0 ] method6_in1_a;
  wire   [ 3 : 0 ] method6_in1_b;
  wire   [ 2 : 0 ] method6_in1_c_x;
  wire   [ 3 : 0 ] method6_in1_c_y;
  wire   [ 3 : 0 ] method6_in1_c_z;

  // ====================
  // Method = method7
  //   ready  => RDY_method7            1   Bit#(1)
  //   result => method7               54   {Vector::Vector#(3, Test4::TS)}
  wire   RDY_method7;
  wire   [ 53 : 0 ] method7;
  wire   [ 2 : 0 ] method7_0_a;  // method7[53:51]
  wire   [ 3 : 0 ] method7_0_b;  // method7[50:47]
  wire   [ 2 : 0 ] method7_0_c_x;  // method7[46:44]
  wire   [ 3 : 0 ] method7_0_c_y;  // method7[43:40]
  wire   [ 3 : 0 ] method7_0_c_z;  // method7[39:36]
  wire   [ 2 : 0 ] method7_1_a;  // method7[35:33]
  wire   [ 3 : 0 ] method7_1_b;  // method7[32:29]
  wire   [ 2 : 0 ] method7_1_c_x;  // method7[28:26]
  wire   [ 3 : 0 ] method7_1_c_y;  // method7[25:22]
  wire   [ 3 : 0 ] method7_1_c_z;  // method7[21:18]
  wire   [ 2 : 0 ] method7_2_a;  // method7[17:15]
  wire   [ 3 : 0 ] method7_2_b;  // method7[14:11]
  wire   [ 2 : 0 ] method7_2_c_x;  // method7[10:8]
  wire   [ 3 : 0 ] method7_2_c_y;  // method7[7:4]
  wire   [ 3 : 0 ] method7_2_c_z;  // method7[3:0]

  // ====================
  // Method = method8
  //   ready  => RDY_method8            1   Bit#(1)
  //   enable => EN_method8             1   Bit#(1)
  //   result => method8                4   ActionValue#(Bit#(4))
  wire   RDY_method8;
  wire   EN_method8;
  wire   [ 3 : 0 ] method8;

  // ====================
  // Method = method9
  //   ready  => RDY_method9            1   Bit#(1)
  //   enable => EN_method9             1   Bit#(1)
  //   result => method9                4   ActionValue#(Bit#(4))
  //   input  => method9_in1            4   Bit#(4)
  wire   RDY_method9;
  wire   EN_method9;
  wire   [ 3 : 0 ] method9;
  wire   [ 3 : 0 ] method9_in1;

  // ====================
  // Method = method10
  //   ready  => RDY_method10           1   Bit#(1)
  //   result => method10             216   {Vector::Vector#(3, Vector::Vector#(4, Test4::TS))}
  wire   RDY_method10;
  wire   [ 215 : 0 ] method10;
  wire   [ 2 : 0 ] method10_0_0_a;  // method10[215:213]
  wire   [ 3 : 0 ] method10_0_0_b;  // method10[212:209]
  wire   [ 2 : 0 ] method10_0_0_c_x;  // method10[208:206]
  wire   [ 3 : 0 ] method10_0_0_c_y;  // method10[205:202]
  wire   [ 3 : 0 ] method10_0_0_c_z;  // method10[201:198]
  wire   [ 2 : 0 ] method10_0_1_a;  // method10[197:195]
  wire   [ 3 : 0 ] method10_0_1_b;  // method10[194:191]
  wire   [ 2 : 0 ] method10_0_1_c_x;  // method10[190:188]
  wire   [ 3 : 0 ] method10_0_1_c_y;  // method10[187:184]
  wire   [ 3 : 0 ] method10_0_1_c_z;  // method10[183:180]
  wire   [ 2 : 0 ] method10_0_2_a;  // method10[179:177]
  wire   [ 3 : 0 ] method10_0_2_b;  // method10[176:173]
  wire   [ 2 : 0 ] method10_0_2_c_x;  // method10[172:170]
  wire   [ 3 : 0 ] method10_0_2_c_y;  // method10[169:166]
  wire   [ 3 : 0 ] method10_0_2_c_z;  // method10[165:162]
  wire   [ 2 : 0 ] method10_0_3_a;  // method10[161:159]
  wire   [ 3 : 0 ] method10_0_3_b;  // method10[158:155]
  wire   [ 2 : 0 ] method10_0_3_c_x;  // method10[154:152]
  wire   [ 3 : 0 ] method10_0_3_c_y;  // method10[151:148]
  wire   [ 3 : 0 ] method10_0_3_c_z;  // method10[147:144]
  wire   [ 2 : 0 ] method10_1_0_a;  // method10[143:141]
  wire   [ 3 : 0 ] method10_1_0_b;  // method10[140:137]
  wire   [ 2 : 0 ] method10_1_0_c_x;  // method10[136:134]
  wire   [ 3 : 0 ] method10_1_0_c_y;  // method10[133:130]
  wire   [ 3 : 0 ] method10_1_0_c_z;  // method10[129:126]
  wire   [ 2 : 0 ] method10_1_1_a;  // method10[125:123]
  wire   [ 3 : 0 ] method10_1_1_b;  // method10[122:119]
  wire   [ 2 : 0 ] method10_1_1_c_x;  // method10[118:116]
  wire   [ 3 : 0 ] method10_1_1_c_y;  // method10[115:112]
  wire   [ 3 : 0 ] method10_1_1_c_z;  // method10[111:108]
  wire   [ 2 : 0 ] method10_1_2_a;  // method10[107:105]
  wire   [ 3 : 0 ] method10_1_2_b;  // method10[104:101]
  wire   [ 2 : 0 ] method10_1_2_c_x;  // method10[100:98]
  wire   [ 3 : 0 ] method10_1_2_c_y;  // method10[97:94]
  wire   [ 3 : 0 ] method10_1_2_c_z;  // method10[93:90]
  wire   [ 2 : 0 ] method10_1_3_a;  // method10[89:87]
  wire   [ 3 : 0 ] method10_1_3_b;  // method10[86:83]
  wire   [ 2 : 0 ] method10_1_3_c_x;  // method10[82:80]
  wire   [ 3 : 0 ] method10_1_3_c_y;  // method10[79:76]
  wire   [ 3 : 0 ] method10_1_3_c_z;  // method10[75:72]
  wire   [ 2 : 0 ] method10_2_0_a;  // method10[71:69]
  wire   [ 3 : 0 ] method10_2_0_b;  // method10[68:65]
  wire   [ 2 : 0 ] method10_2_0_c_x;  // method10[64:62]
  wire   [ 3 : 0 ] method10_2_0_c_y;  // method10[61:58]
  wire   [ 3 : 0 ] method10_2_0_c_z;  // method10[57:54]
  wire   [ 2 : 0 ] method10_2_1_a;  // method10[53:51]
  wire   [ 3 : 0 ] method10_2_1_b;  // method10[50:47]
  wire   [ 2 : 0 ] method10_2_1_c_x;  // method10[46:44]
  wire   [ 3 : 0 ] method10_2_1_c_y;  // method10[43:40]
  wire   [ 3 : 0 ] method10_2_1_c_z;  // method10[39:36]
  wire   [ 2 : 0 ] method10_2_2_a;  // method10[35:33]
  wire   [ 3 : 0 ] method10_2_2_b;  // method10[32:29]
  wire   [ 2 : 0 ] method10_2_2_c_x;  // method10[28:26]
  wire   [ 3 : 0 ] method10_2_2_c_y;  // method10[25:22]
  wire   [ 3 : 0 ] method10_2_2_c_z;  // method10[21:18]
  wire   [ 2 : 0 ] method10_2_3_a;  // method10[17:15]
  wire   [ 3 : 0 ] method10_2_3_b;  // method10[14:11]
  wire   [ 2 : 0 ] method10_2_3_c_x;  // method10[10:8]
  wire   [ 3 : 0 ] method10_2_3_c_y;  // method10[7:4]
  wire   [ 3 : 0 ] method10_2_3_c_z;  // method10[3:0]


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
  assign method6_in1[17:15] = method6_in1_a;
  assign method6_in1[14:11] = method6_in1_b;
  assign method6_in1[10:8] = method6_in1_c_x;
  assign method6_in1[7:4] = method6_in1_c_y;
  assign method6_in1[3:0] = method6_in1_c_z;
  assign method7_0_a = method7[53:51];
  assign method7_0_b = method7[50:47];
  assign method7_0_c_x = method7[46:44];
  assign method7_0_c_y = method7[43:40];
  assign method7_0_c_z = method7[39:36];
  assign method7_1_a = method7[35:33];
  assign method7_1_b = method7[32:29];
  assign method7_1_c_x = method7[28:26];
  assign method7_1_c_y = method7[25:22];
  assign method7_1_c_z = method7[21:18];
  assign method7_2_a = method7[17:15];
  assign method7_2_b = method7[14:11];
  assign method7_2_c_x = method7[10:8];
  assign method7_2_c_y = method7[7:4];
  assign method7_2_c_z = method7[3:0];
  assign method10_0_0_a = method10[215:213];
  assign method10_0_0_b = method10[212:209];
  assign method10_0_0_c_x = method10[208:206];
  assign method10_0_0_c_y = method10[205:202];
  assign method10_0_0_c_z = method10[201:198];
  assign method10_0_1_a = method10[197:195];
  assign method10_0_1_b = method10[194:191];
  assign method10_0_1_c_x = method10[190:188];
  assign method10_0_1_c_y = method10[187:184];
  assign method10_0_1_c_z = method10[183:180];
  assign method10_0_2_a = method10[179:177];
  assign method10_0_2_b = method10[176:173];
  assign method10_0_2_c_x = method10[172:170];
  assign method10_0_2_c_y = method10[169:166];
  assign method10_0_2_c_z = method10[165:162];
  assign method10_0_3_a = method10[161:159];
  assign method10_0_3_b = method10[158:155];
  assign method10_0_3_c_x = method10[154:152];
  assign method10_0_3_c_y = method10[151:148];
  assign method10_0_3_c_z = method10[147:144];
  assign method10_1_0_a = method10[143:141];
  assign method10_1_0_b = method10[140:137];
  assign method10_1_0_c_x = method10[136:134];
  assign method10_1_0_c_y = method10[133:130];
  assign method10_1_0_c_z = method10[129:126];
  assign method10_1_1_a = method10[125:123];
  assign method10_1_1_b = method10[122:119];
  assign method10_1_1_c_x = method10[118:116];
  assign method10_1_1_c_y = method10[115:112];
  assign method10_1_1_c_z = method10[111:108];
  assign method10_1_2_a = method10[107:105];
  assign method10_1_2_b = method10[104:101];
  assign method10_1_2_c_x = method10[100:98];
  assign method10_1_2_c_y = method10[97:94];
  assign method10_1_2_c_z = method10[93:90];
  assign method10_1_3_a = method10[89:87];
  assign method10_1_3_b = method10[86:83];
  assign method10_1_3_c_x = method10[82:80];
  assign method10_1_3_c_y = method10[79:76];
  assign method10_1_3_c_z = method10[75:72];
  assign method10_2_0_a = method10[71:69];
  assign method10_2_0_b = method10[68:65];
  assign method10_2_0_c_x = method10[64:62];
  assign method10_2_0_c_y = method10[61:58];
  assign method10_2_0_c_z = method10[57:54];
  assign method10_2_1_a = method10[53:51];
  assign method10_2_1_b = method10[50:47];
  assign method10_2_1_c_x = method10[46:44];
  assign method10_2_1_c_y = method10[43:40];
  assign method10_2_1_c_z = method10[39:36];
  assign method10_2_2_a = method10[35:33];
  assign method10_2_2_b = method10[32:29];
  assign method10_2_2_c_x = method10[28:26];
  assign method10_2_2_c_y = method10[25:22];
  assign method10_2_2_c_z = method10[21:18];
  assign method10_2_3_a = method10[17:15];
  assign method10_2_3_b = method10[14:11];
  assign method10_2_3_c_x = method10[10:8];
  assign method10_2_3_c_y = method10[7:4];
  assign method10_2_3_c_z = method10[3:0];
`endif

`ifndef __EXPANDPORTS_DONT_CREATE_DUT__
  mkTest4 _mkTest4 ( 
   .CLK( CLK ),
   .RST_N( RST_N ),
   .RDY_method1( RDY_method1 ),
   .EN_method1( EN_method1 ),
   .method1_in1( method1_in1 ),
   .method1_in2( method1_in2 ),
   .RDY_method2( RDY_method2 ),
   .method2( method2 ),
   .method2_in1( method2_in1 ),
   .method2_in2( method2_in2 ),
   .RDY_method3( RDY_method3 ),
   .method3( method3 ),
   .RDY_method4( RDY_method4 ),
   .EN_method4( EN_method4 ),
   .method4( method4 ),
   .method4_in1( method4_in1 ),
   .RDY_method5( RDY_method5 ),
   .EN_method5( EN_method5 ),
   .method5_in1( method5_in1 ),
   .RDY_method6( RDY_method6 ),
   .method6( method6 ),
   .method6_in1( method6_in1 ),
   .RDY_method7( RDY_method7 ),
   .method7( method7 ),
   .RDY_method8( RDY_method8 ),
   .EN_method8( EN_method8 ),
   .method8( method8 ),
   .RDY_method9( RDY_method9 ),
   .EN_method9( EN_method9 ),
   .method9( method9 ),
   .method9_in1( method9_in1 ),
   .RDY_method10( RDY_method10 ),
   .method10( method10 )
  );
`endif
