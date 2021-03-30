// nested structs are not permitted, because they don't have constructor names
// for example, there is no way to create a struct for field "two"

typedef struct {
    Bool one;
    struct {
        Bool left;
        Bool right;
    } two;
} OneTwo;
