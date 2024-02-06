// Copyright(c) 2016.  Atomic Rules LLC.   All rights reserved.

////////////////////////////////////////////////////////////////////////////////
///  IPv4 Header and support types
///  Ed Czeck
///  May 2015
///  for Atomic Rules LLC
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
/// IP Protocol values
////////////////////////////////////////////////////////////////////////////////
typedef enum {
              HOPOPT		= 0
              ,ICMP		= 1
              ,IGMP		= 2
              ,GGP		= 3
              ,IPv4		= 4
              ,ST		= 5
              ,TCP		= 6
              ,CBT		= 7
              ,EGP		= 8
              ,IGP		= 9
              ,BBN_RCC_MON	= 10
              ,NVP_II		= 11
              ,PUP		= 12
              ,ARGUS		= 13
              ,EMCON		= 14
              ,XNET		= 15
              ,CHAOS		= 16
              ,UDP		= 17
              ,MUX		= 18
              ,DCN_MEAS	        = 19
              ,HMP		= 20
              ,PRM		= 21
              ,XNS_IDP		= 22
              ,TRUNK_1		= 23
              ,TRUNK_2		= 24
              ,LEAF_1		= 25
              ,LEAF_2		= 26
              ,RDP		= 27
              ,IRTP		= 28
              ,ISO_TP4    	= 29
              ,NETBLT		= 30
              ,MFE_NSP		= 31
              ,MERIT_INP	= 32
              ,DCCP		= 33
              ,PC_3		= 34
              ,IDPR		= 35
              ,XTP		= 36
              ,DDP		= 37
              ,IDPR_CMTP	= 38
              ,TPplusplus	= 39
              ,IL		= 40
              ,IPv6		= 41
              ,SDRP		= 42
              ,IPv6_Route	= 43
              ,IPv6_Frag	= 44
              ,IDRP		= 45
              ,RSVP		= 46
              ,GRE		= 47
              ,DSR		= 48
              ,BNA		= 49
              ,ESP		= 50
              ,AH		= 51
              ,I_NLSP		= 52
              ,SWIPE		= 53
              ,NARP		= 54
              ,MOBILE		= 55
              ,TLSP		= 56
              ,SKIP		= 57
              ,IPv6_ICMP	= 58
              ,IPv6_NoNxt	= 59
              ,IPv6_Opts	= 60
              ,UA61		= 61
              ,CFTP		= 62
              ,UA63		= 63
              ,SAT_EXPAK	= 64
              ,KRYPTOLAN	= 65
              ,RVD		= 66
              ,IPPC		= 67
              ,UA68		= 68
              ,SAT_MON		= 69
              ,VISA		= 70
              ,IPCV		= 71
              ,CPNX		= 72
              ,CPHB		= 73
              ,WSN		= 74
              ,PVP		= 75
              ,BR_SAT_MON	= 76
              ,SUN_ND		= 77
              ,WB_MON		= 78
              ,WB_EXPAK		= 79
              ,ISO_IP		= 80
              ,VMTP		= 81
              ,SECURE_VMTP	= 82
              ,VINES		= 83
              ,TTP_IPTM		= 84
              ,NSFNET_IGP	= 85
              ,DGP		= 86
              ,TCF		= 87
              ,EIGRP		= 88
              ,OSPFIGP		= 89
              ,Sprite_RPC	= 90
              ,LARP		= 91
              ,MTP		= 92
              ,AX_25		= 93
              ,IPIP		= 94
              ,MICP		= 95
              ,SCC_SP		= 96
              ,ETHERIP		= 97
              ,ENCAP		= 98
              ,UA99		= 99
              ,GMTP		= 100
              ,IFMP		= 101
              ,PNNI		= 102
              ,PIM		= 103
              ,ARIS		= 104
              ,SCPS		= 105
              ,QNX		= 106
              ,A_N		= 107
              ,IPComp		= 108
              ,SNP		= 109
              ,Compaq_Peer	= 110
              ,IPX_in_IP	= 111
              ,VRRP		= 112
              ,PGM		= 113
              ,XX114		= 114
              ,L2TP		= 115
              ,DDX		= 116
              ,IATP		= 117
              ,STP		= 118
              ,SRP		= 119
              ,UTI		= 120
              ,SMP		= 121
              ,SM		= 122
              ,PTP		= 123
              ,ISIS		= 124
              ,FIRE		= 125
              ,CRTP		= 126
              ,CRUDP		= 127
              ,SSCOPMCE		= 128
              ,IPLT		= 129
              ,SPS		= 130
              ,PIPE		= 131
              ,SCTP		= 132
              ,FC		= 133
              ,RSVP_E2E_IGNORE	= 134
              ,Mobility_Header	= 135
              ,UDPLite	        = 136
              ,MPLS_in_IP	= 137
              ,Manet		= 138
              ,HIP		= 139
              ,Shi		= 140
              ,WESP		= 141
              ,ROHC		= 142
              // Unassigned
              ,UA143   = 143  ,UA144   = 144  ,UA145   = 145  ,UA146   = 146
              ,UA147   = 147  ,UA148   = 148  ,UA149   = 149  ,UA150   = 150
              ,UA151   = 151  ,UA152   = 152  ,UA153   = 153  ,UA154   = 154
              ,UA155   = 155  ,UA156   = 156  ,UA157   = 157  ,UA158   = 158
              ,UA159   = 159  ,UA160   = 160  ,UA161   = 161  ,UA162   = 162
              ,UA163   = 163  ,UA164   = 164  ,UA165   = 165  ,UA166   = 166
              ,UA167   = 167  ,UA168   = 168  ,UA169   = 169  ,UA170   = 170
              ,UA171   = 171  ,UA172   = 172  ,UA173   = 173  ,UA174   = 174
              ,UA175   = 175  ,UA176   = 176  ,UA177   = 177  ,UA178   = 178
              ,UA179   = 179  ,UA180   = 180  ,UA181   = 181  ,UA182   = 182
              ,UA183   = 183  ,UA184   = 184  ,UA185   = 185  ,UA186   = 186
              ,UA187   = 187  ,UA188   = 188  ,UA189   = 189  ,UA190   = 190
              ,UA191   = 191  ,UA192   = 192  ,UA193   = 193  ,UA194   = 194
              ,UA195   = 195  ,UA196   = 196  ,UA197   = 197  ,UA198   = 198
              ,UA199   = 199  ,UA200   = 200  ,UA201   = 201  ,UA202   = 202
              ,UA203   = 203  ,UA204   = 204  ,UA205   = 205  ,UA206   = 206
              ,UA207   = 207  ,UA208   = 208  ,UA209   = 209  ,UA210   = 210
              ,UA211   = 211  ,UA212   = 212  ,UA213   = 213  ,UA214   = 214
              ,UA215   = 215  ,UA216   = 216  ,UA217   = 217  ,UA218   = 218
              ,UA219   = 219  ,UA220   = 220  ,UA221   = 221  ,UA222   = 222
              ,UA223   = 223  ,UA224   = 224  ,UA225   = 225  ,UA226   = 226
              ,UA227   = 227  ,UA228   = 228  ,UA229   = 229  ,UA230   = 230
              ,UA231   = 231  ,UA232   = 232  ,UA233   = 233  ,UA234   = 234
              ,UA235   = 235  ,UA236   = 236  ,UA237   = 237  ,UA238   = 238
              ,UA239   = 239  ,UA240   = 240  ,UA241   = 241  ,UA242   = 242
              ,UA243   = 243  ,UA244   = 244  ,UA245   = 245  ,UA246   = 246
              ,UA247   = 247  ,UA248   = 248  ,UA249   = 249  ,UA250   = 250
              ,UA251   = 251  ,UA252   = 252  ,UA253   = 253  ,UA254   = 254
              ,Reserved		= 255
              } IPProtocol deriving (Bits, Eq);

// We derive our own version of FShow here to speed compiles.
// bsc does not like decoding big enums
instance FShow#(IPProtocol);
   function Fmt fshow (IPProtocol p);
   UInt#(8) px = unpack(pack(p));
   return
      case (p)
         ICMP     : return $format("ICMP");
         IGMP     : return $format("IGMP");
         UDP     : return $format("UDP");
         TCP     : return $format("TCP");
         default : return $format ("P%0d", px);
      endcase;
   endfunction
endinstance


