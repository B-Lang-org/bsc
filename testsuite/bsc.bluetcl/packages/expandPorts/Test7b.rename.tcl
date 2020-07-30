global renameList
set renameList [list \
                    { CLK_c1    system_clock_1 } \
                    { pIn       funky_input } \
                    { CLK       system_clock } \
                    { RST_N     reset_n } \
                    \
                    { ifcA_0_method1_in1   I0_M1_in1 } \
                    { ifcA_0_method1_in2   I0_M1_in2 } \
                    { EN_ifcA_0_method1    I0_M1_enable } \
                    { RDY_ifcA_0_method1   I0_M1_ready } \
                    \
                    { ifcA_0_method2_in1   I0_M2_in1 } \
                    { ifcA_0_method2_in2   I0_M2_in2 } \
                    { ifcA_0_method2       I0_M2_output } \
                    { RDY_ifcA_0_method2   I0_M2_ready } \
                    \
                    { ifcA_1_method1_in1   I1_M1_in1 } \
                    { ifcA_1_method1_in2   I1_M1_in2 } \
                    { EN_ifcA_1_method1    I1_M1_enable } \
                    { RDY_ifcA_1_method1   I1_M1_ready } \
                    \
                    { ifcA_1_method2_in1   I1_M2_in1 } \
                    { ifcA_1_method2_in2   I1_M2_in2 } \
                    { ifcA_1_method2       I1_M2_output } \
                    { RDY_ifcA_1_method2   I1_M2_ready } \
                    ]

