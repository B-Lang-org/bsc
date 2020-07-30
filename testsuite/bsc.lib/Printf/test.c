// This C file is for comparing the output of sprintf in C with the output
// of sprintf in BSV.

#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {

    printf("#---- No format\n");
    printf("Hello World!\n");

    printf("#---- %%%%\n");
    printf("%% %% %%\n");

    printf("#---- %%c %%C\n");
    {
      char c1 = 'x';
      char c2 = 'W';
      char c3 = '*';
      printf("%c %c %c, %C %C %C\n", c1, c2, c3, c1, c2, c3);
    }

    printf("#---- %%s %%S\n");
    {
      char *s1 = "Hello World!";
      char *s2 = "";
      printf("'%s' '%s', '%s' '%s'\n", s1, s2, s1, s2);
    }

    int i1 = 8;
    int i2 = 1234567890;
    int i3 = 0;
    int i4 = -17;

    unsigned int u1 = 8;
    unsigned int u2 = 1234567890;
    unsigned int u3 = 0;

    printf("#---- %%d\n");
    {
      printf("Integer '%d' '%d' '%d' '%d'\n", i1, i2, i3, i4);
      printf("Bit     '%d' '%d' '%d'\n", u1, u2, u3);
      printf("UInt    '%d' '%d' '%d'\n", u1, u2, u3);
      printf("Int     '%d' '%d' '%d' '%d'\n", i1, i2, i3, i4);
    }

    printf("#---- %%D\n");
    {
      printf("'%d' '%d' '%d' '%d'\n", i1, i2, i3, i4);
    }

    printf("#---- %%i\n");
    {
      printf("'%d' '%d' '%d' '%d'\n", i1, i2, i3, i4);
    }

    printf("#---- %%I\n");
    {
      printf("'%d' '%d' '%d' '%d'\n", i1, i2, i3, i4);
    }

    printf("#---- %%+d\n");
    {
      printf("'%+d' '%+d' '%+d' '%+d'\n", i1, i2, i3, i4);
    }

    printf("#---- %%-8d\n");
    {
      printf("Integer '%-8d' '%-8d' '%-8d' '%-8d'\n", i1, i2, i3, i4);
      printf("Bit     '%-8d' '%-8d' '%-8d'\n", u1, u2, u3);
      printf("UInt    '%-8d' '%-8d' '%-8d'\n", u1, u2, u3);
      printf("Int     '%-8d' '%-8d' '%-8d' '%-8d'\n", i1, i2, i3, i4);
    }

    printf("#---- %%4d\n");
    {
      printf("Integer '%4d' '%4d' '%4d' '%4d'\n", i1, i2, i3, i4);
      printf("Bit     '%4d' '%4d' '%4d'\n", u1, u2, u3);
      printf("UInt    '%4d' '%4d' '%4d'\n", u1, u2, u3);
      printf("Int     '%4d' '%4d' '%4d' '%4d'\n", i1, i2, i3, i4);
    }

    printf("#---- %%.4d\n");
    {
      printf("Integer '%.4d' '%.4d' '%.4d' '%.4d'\n", i1, i2, i3, i4);
      printf("Bit     '%.4d' '%.4d' '%.4d'\n", u1, u2, u3);
      printf("UInt    '%.4d' '%.4d' '%.4d'\n", u1, u2, u3);
      printf("Int     '%.4d' '%.4d' '%.4d' '%.4d'\n", i1, i2, i3, i4);
    }

    printf("#---- %%04d\n");
    {
      printf("Integer '%04d' '%04d' '%04d' '%04d'\n", i1, i2, i3, i4);
      printf("Bit     '%04d' '%04d' '%04d'\n", u1, u2, u3);
      printf("UInt    '%04d' '%04d' '%04d'\n", u1, u2, u3);
      printf("Int     '%04d' '%04d' '%04d' '%04d'\n", i1, i2, i3, i4);
    }

    printf("#---- %%*d\n");
    {
      printf("Integer '%*d' '%*d' '%*d' '%*d'\n", 5, i1, 5, i2, 5, i3, 5, i4);
      printf("Bit     '%*d' '%*d' '%*d'\n", 5, u1, 5, u2, 5, u3);
      printf("UInt    '%*d' '%*d' '%*d'\n", 5, u1, 5, u2, 5, u3);
      printf("Int     '%*d' '%*d' '%*d' '%*d'\n", 5, i1, 5, i2, 5, i3, 5, i4);
    }

    printf("#---- %%o\n");
    {
      printf("Integer '%o' '%o' '%o'\n", i1, i2, i3);
      printf("Bit     '%o' '%o' '%o'\n", u1, u2, u3);
      printf("UInt    '%o' '%o' '%o'\n", u1, u2, u3);
      printf("Int     '%o' '%o' '%o' '%o'\n", i1, i2, i3, i4);
    }

    printf("#---- %%O\n");
    {
      printf("'%o' '%o' '%o'\n", i1, i2, i3);
    }

    printf("#---- %%-8o\n");
    {
      printf("Integer '%-8o' '%-8o' '%-8o'\n", i1, i2, i3);
      printf("Bit     '%-8o' '%-8o' '%-8o'\n", u1, u2, u3);
      printf("UInt    '%-8o' '%-8o' '%-8o'\n", u1, u2, u3);
      printf("Int     '%-8o' '%-8o' '%-8o' '%-8o'\n", i1, i2, i3, i4);
    }

    printf("#---- %%4o\n");
    {
      printf("Integer '%4o' '%4o' '%4o'\n", i1, i2, i3);
      printf("Bit     '%4o' '%4o' '%4o'\n", u1, u2, u3);
      printf("UInt    '%4o' '%4o' '%4o'\n", u1, u2, u3);
      printf("Int     '%4o' '%4o' '%4o' '%4o'\n", i1, i2, i3, i4);
    }

    printf("#---- %%.4o\n");
    {
      printf("Integer '%.4o' '%.4o' '%.4o'\n", i1, i2, i3);
      printf("Bit     '%.4o' '%.4o' '%.4o'\n", u1, u2, u3);
      printf("UInt    '%.4o' '%.4o' '%.4o'\n", u1, u2, u3);
      printf("Int     '%.4o' '%.4o' '%.4o' '%.4o'\n", i1, i2, i3, i4);
    }

    printf("#---- %%04o\n");
    {
      printf("Integer '%04o' '%04o' '%04o'\n", i1, i2, i3);
      printf("Bit     '%04o' '%04o' '%04o'\n", u1, u2, u3);
      printf("UInt    '%04o' '%04o' '%04o'\n", u1, u2, u3);
      printf("Int     '%04o' '%04o' '%04o' '%04o'\n", i1, i2, i3, i4);
    }

    printf("#---- %%*o\n");
    {
      printf("Integer '%*o' '%*o' '%*o'\n", 5, i1, 5, i2, 5, i3);
      printf("Bit     '%*o' '%*o' '%*o'\n", 5, u1, 5, u2, 5, u3);
      printf("UInt    '%*o' '%*o' '%*o'\n", 5, u1, 5, u2, 5, u3);
      printf("Int     '%*o' '%*o' '%*o' '%*o'\n", 5, i1, 5, i2, 5, i3, 5, i4);
    }

    printf("#---- %%x\n");
    {
      printf("Integer '%x' '%x' '%x'\n", i1, i2, i3);
      printf("Bit     '%x' '%x' '%x'\n", u1, u2, u3);
      printf("UInt    '%x' '%x' '%x'\n", u1, u2, u3);
      printf("Int     '%x' '%x' '%x' '%x'\n", i1, i2, i3, i4);
    }

    printf("#---- %%X\n");
    {
      printf("'%X' '%X' '%X'\n", i1, i2, i3);
    }

    printf("#---- %%h\n");
    {
      printf("'%x' '%x' '%x'\n", i1, i2, i3);
    }

    printf("#---- %%H\n");
    {
      printf("'%X' '%X' '%X'\n", i1, i2, i3);
    }

    printf("#---- %%-8x\n");
    {
      printf("Integer '%-8x' '%-8x' '%-8x'\n", i1, i2, i3);
      printf("Bit     '%-8x' '%-8x' '%-8x'\n", u1, u2, u3);
      printf("UInt    '%-8x' '%-8x' '%-8x'\n", u1, u2, u3);
      printf("Int     '%-8x' '%-8x' '%-8x' '%-8x'\n", i1, i2, i3, i4);
    }

    printf("#---- %%4x\n");
    {
      printf("Integer '%4x' '%4x' '%4x'\n", i1, i2, i3);
      printf("Bit     '%4x' '%4x' '%4x'\n", u1, u2, u3);
      printf("UInt    '%4x' '%4x' '%4x'\n", u1, u2, u3);
      printf("Int     '%4x' '%4x' '%4x' '%4x'\n", i1, i2, i3, i4);
    }

    printf("#---- %%.4x\n");
    {
      printf("Integer '%.4x' '%.4x' '%.4x'\n", i1, i2, i3);
      printf("Bit     '%.4x' '%.4x' '%.4x'\n", u1, u2, u3);
      printf("UInt    '%.4x' '%.4x' '%.4x'\n", u1, u2, u3);
      printf("Int     '%.4x' '%.4x' '%.4x' '%.4x'\n", i1, i2, i3, i4);
    }

    printf("#---- %%04x\n");
    {
      printf("Integer '%04x' '%04x' '%04x'\n", i1, i2, i3);
      printf("Bit     '%04x' '%04x' '%04x'\n", u1, u2, u3);
      printf("UInt    '%04x' '%04x' '%04x'\n", u1, u2, u3);
      printf("Int     '%04x' '%04x' '%04x' '%04x'\n", i1, i2, i3, i4);
    }

    printf("#---- %%*x\n");
    {
      printf("Integer '%*x' '%*x' '%*x'\n", 5, i1, 5, i2, 5, i3);
      printf("Bit     '%*x' '%*x' '%*x'\n", 5, u1, 5, u2, 5, u3);
      printf("UInt    '%*x' '%*x' '%*x'\n", 5, u1, 5, u2, 5, u3);
      printf("Int     '%*x' '%*x' '%*x' '%*x'\n", 5, i1, 5, i2, 5, i3, 5, i4);
    }

    double r1 = 0.0;
    double r2 = - 1.7;
    double r3 = 10.0 / 3.0;
    double r4 = -1e23 / 8.0;
    double r5 = 12345e-20;

    printf("#---- %%f %%F\n");
    {
      printf("'%f' '%f' '%f' '%f' '%f'\n", r1, r2, r3, r4, r5);
      printf("'%F' '%F' '%F' '%F' '%F'\n", r1, r2, r3, r4, r5);
    }

    printf("#---- %%e %%E\n");
    {
      printf("'%e' '%e' '%e' '%e' '%e'\n", r1, r2, r3, r4, r5);
      printf("'%E' '%E' '%E' '%E' '%E'\n", r1, r2, r3, r4, r5);
    }

    printf("#---- %%g %%G\n");
    {
      printf("'%g' '%g' '%g' '%g' '%g'\n", r1, r2, r3, r4, r5);
      printf("'%G' '%G' '%G' '%G' '%G'\n", r1, r2, r3, r4, r5);
    }

    printf("#---- %%.6f %%.6F\n");
    {
      printf("'%.6f' '%.6f' '%.6f' '%.6f' '%.6f'\n", r1, r2, r3, r4, r5);
      printf("'%.6F' '%.6F' '%.6F' '%.6F' '%.6F'\n", r1, r2, r3, r4, r5);
    }

    printf("#---- %%.6e %%.6E\n");
    {
      printf("'%.6e' '%.6e' '%.6e' '%.6e' '%.6e'\n", r1, r2, r3, r4, r5);
      printf("'%.6E' '%.6E' '%.6E' '%.6E' '%.6E'\n", r1, r2, r3, r4, r5);
    }

    exit(0);
}

