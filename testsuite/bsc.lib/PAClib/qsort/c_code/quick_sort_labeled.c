#include <stdio.h>


int partition(int a[], int l, int r) {
   int v = a[r];
   int i = l - 1;
   int j = r;
   int t;

   for (;;) {

      mkPartitionLoop_preTest : {
         i = i + 1;
         j = j - 1;
         while (a[i] < v) i++;
         while (a[j] > v) j--;
      } // end of mkPartitionLoop_preTest

      if (i >= j) break;

      partitionLoop_postTest : {
         t = a[i]; a[i] = a[j]; a[j] = t;
      } // end of partitionLoop_postTest
   }

   partitionLoop_final : {
      t = a[i]; a[i] = a[r]; a[r] = t;
   } // end of partitionLoop_final

   return i;
}

void quick_sort(int a[], int n) {
   int l, r, v;
   int leftstack[32], rightstack[32];
   int sp = 1;
   leftstack[0] = 0;
   rightstack[0] = n - 1;

   while (sp != 0) { // mainLoop_preTest

      mkMainLoop_postTest : {

         decrement_sp : {
            sp--;
         } // end of decrement_sp

         mkTruePath : if (leftstack[sp] < rightstack[sp]) {

            mkPartition : {
               v = partition(a, leftstack[sp], rightstack[sp]);
            } // end of mkPartition

            update_stack : {
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
            } // end of update_stack

         } // end of mkTruePath

      } // end of mkMainLoop_postTest

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
