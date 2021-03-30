typedef struct {
    Bit#(8) red;
    Bit#(8) green;
    Bit#(8) blue;
} RgbColor;

// XXX SV doesn't have RgbColor in the initializer but this is beyond BSV 0.5
// XXX SV would permit red = { 255, 0, 0 }
RgbColor red;
red = RgbColor { red:255, green:0, blue:0 };
