#include <stdio.h>


int partition(int a[], int l, int r) {
   int v = a[r];
   int i = l - 1;
   int j = r;
   int t;
   for (;;) {
      i = i + 1;
      j = j - 1;
      while (a[i] < v) i++;
      while (a[j] > v) j--;
      if (i >= j) break;
      t = a[i]; a[i] = a[j]; a[j] = t;
   }
   t = a[i]; a[i] = a[r]; a[r] = t;
   return i;
}

void quick_sort(int a[], int n) {
   int l, r, v;
   int leftstack[32], rightstack[32];
   int sp = 1;
   leftstack[0] = 0;
   rightstack[0] = n - 1;
   while (sp != 0) {
      sp--;
      if (leftstack[sp] < rightstack[sp]) {
         v = partition(a, leftstack[sp], rightstack[sp]);
         l = leftstack[sp];
         r = rightstack[sp];
         if (v-l < r-v) {
            leftstack[sp] = v + 1;
            rightstack[sp] = r;
            sp++;
            leftstack[sp] = l;
            rightstack[sp] = v - 1;
            sp++;
         }
         else {
            leftstack[sp] = l;
            rightstack[sp] = v - 1;
            sp++;
            leftstack[sp] = v + 1;
            rightstack[sp] = r;
            sp++;
         }
      }
   }
}

int main() {

   int inData[16] = { 53, 101, 120,  10,  91, 250,  19,  8,
                     651,  22, 544,  87,  20, 199,  76, 33};
   int outData[16];
   int i;

   quick_sort(inData, 16);

   for (i=0; i<16; i++)
      printf("%d\n", inData[i]);

   return 0;
}
