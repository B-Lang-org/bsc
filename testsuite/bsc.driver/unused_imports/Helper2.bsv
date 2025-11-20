// Second helper package with a constructor that has the same name as Helper's

package Helper2;

// Different Color type with same constructor names
typedef enum {
    Red,
    Yellow
} Color deriving (Eq, Bits);

export Color(..);

endpackage
