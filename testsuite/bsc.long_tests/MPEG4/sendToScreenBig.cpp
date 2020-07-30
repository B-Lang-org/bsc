#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <gtk/gtk.h>
#include <assert.h>

typedef unsigned char u8;

void cxx_sendToScreen( u8 data );
extern "C" {
  void sendToScreen( u8 data ) { cxx_sendToScreen( data ); }
}

int init = 0;

#define IMAGE_WIDTH	176
#define IMAGE_HEIGHT	144
#define sizeX           IMAGE_WIDTH
#define sizeY           IMAGE_HEIGHT

u8 yBuffer[sizeX][sizeY];
u8 uBuffer[sizeX][sizeY];
u8 vBuffer[sizeX][sizeY];

#define zoom 2
int antialias = 0;

//////////////////////////////////////////////////////////////////////
// align?
guchar rgbbuf1[sizeY*sizeX*3];             // original size
guchar rgbbuf2[sizeY*zoom][sizeX*zoom][3]; // zoom
guchar rgbbuf3[sizeY*zoom][sizeX*zoom][3]; // antialias
guchar rgbbuf3_end;

//////////////////////////////////////////////////////////////////////

gboolean on_darea_expose (GtkWidget *widget,
                          GdkEventExpose *event,
                          gpointer user_data)
{
    gdk_draw_rgb_image (widget->window, widget->style->fg_gc[GTK_STATE_NORMAL],
                        0, 0, sizeX*zoom, sizeY*zoom,
                        GDK_RGB_DITHER_MAX, (guchar*)((void*)(&rgbbuf2)), sizeX * 3 * zoom);

  return TRUE;
}

//////////////////////////////////////////////////////////////////////
u8 clamp( float in ) {
  if (in < 0) return 0;
  if (in > 255) return 255;
  return (int)in;
}

//////////////////////////////////////////////////////////////////////
GtkWidget *window, *darea;
char m1 = 'r';
char m2 = 'g';
char m3 = 'b';
int testmode = 0;
int stopframe = 420;
bool help = false;

void* drawScreenInit() {
  gtk_init (0, NULL);

  window = gtk_window_new (GTK_WINDOW_TOPLEVEL);

  darea = gtk_drawing_area_new ();

  gtk_widget_set_size_request (darea, sizeX*zoom, sizeY*zoom);

  gtk_container_add (GTK_CONTAINER (window), darea);

  gtk_signal_connect (GTK_OBJECT (darea), "expose-event",
                      GTK_SIGNAL_FUNC (on_darea_expose), NULL);

  gtk_widget_show_all (window);

  return NULL;
}

//////////////////////////////////////////////////////////////////////
void cxx_sendToScreen( u8 data ) {
    
  // write via pipes
  if (init == 0) {
    init = 1;
    drawScreenInit();
    printf("Screen initialized\n");
  }

  // get lock, find right place to put this
  static int bp = 0;
  static int x = 0;
  static int y = 0;
    
  switch (bp) {

  case 0: {
    yBuffer[x][y] =  data;
    x += 1;
    if (x >= sizeX) { x = 0; y += 1; if (y >= sizeY) { y = 0; bp = 1; } }
    break;
  }

  case 1: {
    uBuffer[x][y] =  data;
    x += 2;
    if (x >= sizeX) { x = 0; y += 2; if (y >= sizeY) { y = 0; bp = 2; } }
    break;
  }

  case 2: { 
    vBuffer[x][y] =  data;
    x += 2;
    if (x >= sizeX) { 
      x = 0; 
      y += 2; 
      if (y >= sizeY) { 
        y = 0; 
        bp = 0; 
          
        //////////////////////////////////////////////////////////////////////
        // draw one screen
        static int i = 0;
        if (i >= stopframe) {
          printf ("Done...\n");
          exit(1);
        }

        gtk_main_iteration_do ( false );
        
        ////////////////////////////////////////////////////////////
        // Convert YUV to RGB buffer.
        guchar* beg_rgbbuf1 = (guchar*)((void*)(&rgbbuf1));
        guchar* eos_rgbbuf1 = (guchar*)((void*)(&rgbbuf2));
        guchar* beg_rgbbuf2 = (guchar*)((void*)(&rgbbuf2));
        guchar* eos_rgbbuf2 = (guchar*)((void*)(&rgbbuf3));
        guchar* beg_rgbbuf3 = (guchar*)((void*)(&rgbbuf3));
        guchar* eos_rgbbuf3 = (guchar*)((void*)(&rgbbuf3_end));

        guchar *pos = beg_rgbbuf1;
        for (gint y = 0; y < sizeY; y++) {
          for (gint x = 0; x < sizeX; x++) {
            int x2 = x & ~1;
            int y2 = y & ~1;
            
            float Yi = yBuffer[x][y];
            float Ui = uBuffer[x2][y2];
            float Vi = vBuffer[x2][y2];
            
            // convert to rgb
            float Y = Yi - 16;
            float U = Ui - 128;
            float V = Vi - 128;
            
            u8 r = clamp( 1.164 * Y + 1.596*V);
            u8 g = clamp( 1.164 * Y - 0.813*V - 0.392*U );
            u8 b = clamp( 1.164 * Y + 2.017*U );
            
            // general this will be rgb, but testmodes allow others!
            *pos++ = r; // getColor( m1, r,g,b, Yi,Ui,Vi );
            *pos++ = g; // getColor( m2, r,g,b, Yi,Ui,Vi );
            *pos++ = b; // getColor( m3, r,g,b, Yi,Ui,Vi );
          }
        }

        if (pos != eos_rgbbuf1) {
          printf("ERROR: pos(%x) != eos_rgbbuf1(%x)\n", pos, eos_rgbbuf1);
          exit(1);
        }

        guchar *pos1 = beg_rgbbuf1;
        guchar *pos2 = beg_rgbbuf2;

        ////////////////////////////////////////////////////////////
        // resample for zoom
        for (gint y = 0; y < sizeY*zoom; y+=zoom) {
          for (gint x = 0; x < sizeX*zoom; x+=zoom) {
            for (gint c = 0; c < 3; c++) {
              switch (zoom) {
              case 1: {
                rgbbuf2[y]  [x]  [c] = *pos1; 
                break;
              }
              case 2: {
                rgbbuf2[y]  [x]  [c] = *pos1;
                rgbbuf2[y]  [x+1][c] = *pos1;
                rgbbuf2[y+1][x  ][c] = *pos1;
                rgbbuf2[y+1][x+1][c] = *pos1++;
                break;
              }
              case 3: {
                rgbbuf2[y]  [x]  [c] = *pos1;
                rgbbuf2[y]  [x+1][c] = *pos1;
                rgbbuf2[y]  [x+2][c] = *pos1;
                rgbbuf2[y+1][x  ][c] = *pos1;
                rgbbuf2[y+1][x+1][c] = *pos1;
                rgbbuf2[y+1][x+2][c] = *pos1;
                rgbbuf2[y+2][x+0][c] = *pos1;
                rgbbuf2[y+2][x+1][c] = *pos1;
                rgbbuf2[y+2][x+2][c] = *pos1++;
                break;
              }

              default: assert(!"zoom 1 or 2 only allowed");
              }
            }
          }
        }

        ////////////////////////////////////////////////////////////
        // 3x3 anti alias
        // memcpy( rgbbuf3, rgbbuf2, sizeX*sizeY*3*zoom*zoom );

        /*
        if (antialias == 1) {
          for (gint y = 0; y < (sizeY*zoom)-zoom; y+=zoom) {
            for (gint x = 0; x < (sizeX*zoom)-zoom; x+=zoom) {
              for (gint c = 0; c < 3; c++) {
                guchar color[3][3];
                int sum;
                // 1,3,1
                // 3,9,3
                // 1,3,1
                // weighted average of the colors

                sum  = rgbbuf2[y]  [x]  [c];
                sum += rgbbuf2[y]  [x+1][c] * 3;
                sum += rgbbuf2[y]  [x+2][c];
                sum += rgbbuf2[y+1][x  ][c] * 3;
                sum += rgbbuf2[y+1][x+1][c] * 9; // center pixel!
                sum += rgbbuf2[y+1][x+2][c] * 3;
                sum += rgbbuf2[y+2][x+0][c];
                sum += rgbbuf2[y+2][x+1][c] * 3;
                sum += rgbbuf2[y+2][x+2][c];

                rgbbuf3[y+1][x+1][c] = sum / (1+3+1+3+9+3+1+3+1);
              }
            }
          }
        }
        */

        ////////////////////////////////////////////////////////////
        gtk_widget_queue_draw_area( darea, 0,0, sizeX*zoom, sizeY*zoom );
        
        // printf("%d\n", i);
        gtk_main_iteration_do ( false );
        
        // wait for screen to draw before returning?
        i++;
      }
    }
  }
  }
}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
#ifdef SELFTEST

int main(int argc, char* argv[]) {
  // open pipe

  FILE* yf = fopen("y.txt", "r");
  FILE* uf = fopen("u.txt", "r");
  FILE* vf = fopen("v.txt", "r");
  int i,j;
  unsigned char c;

  int pixels = sizeX * sizeY;
  int delay = 0 ; // 0x7FF * 3;
  
  if ((yf ==0) || (uf == 0) || (vf == 0)) {
    printf ("ERROR: can't open input files\n");
    exit(-1);
  }

  for (j=1; j<420; j++) {
    // printf ("Frame %d\n", j);

    for (i=0; i<pixels; i++) {
      fscanf(yf, "%x", &c);
      sendToScreen(c);
    }
    for (i=0; i<(pixels/4); i++) {
      fscanf(uf, "%x", &c);
      sendToScreen(c);
    }
    for (i=0; i<(pixels/4); i++) {
      fscanf(vf, "%x", &c);
      sendToScreen(c);
    }
  }
}

#endif

