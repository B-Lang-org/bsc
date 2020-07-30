//import DefaultValue :: *;

// A type which does not have an instance of DefaultValue or Literal
typedef struct { Bit#(8) val; } MyT;

// This matches the catch-all instance for DefaultValue
// which introduces a Literal proviso
MyT x = defaultValue;

