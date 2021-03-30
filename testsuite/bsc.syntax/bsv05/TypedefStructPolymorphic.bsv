typedef struct {
    color red;
    color green;
    color blue;
} RgbColor #(parameter type color);

// XXX SV doesn't have RgbColor in the initializer but this is beyond BSV 0.5
// XXX SV would permit red = { 255, 0, 0 }
RgbColor #(Bit#(8)) red;
red = RgbColor { red:255, green:0, blue:0 };
