/* Exploration only (not a proof dependency).
 *
 * Enumerate turn words w of length P (bit i = 1: the ant reads black at phase i and turns left)
 * that are self-consistent as a white-background periodic orbit of the RL ant:
 *   - after one period the heading is unchanged and the drift v is nonzero;
 *   - on the bi-infinite periodic path pos(kP + j) = pos(j) + k v, at every phase i the colour
 *     read equals the parity of the number of earlier visits m < i (m over all integers) to
 *     pos(i): a cell starts white and every visit flips it.
 * Any eventually periodic run from a finite initial state yields such a word (far enough out,
 * the only cells read are fresh white cells and the run's own trail).  The converse is not
 * claimed.
 *
 * usage: periodic_words PMIN PMAX [check-word]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static const int DX[4] = {0, 1, 0, -1}; /* north, east, south, west */
static const int DY[4] = {1, 0, -1, 0};

static int consistent(const unsigned char *w, int P, int *vx_out, int *vy_out) {
    int px[1024], py[1024];
    int d = 0, x = 0, y = 0;
    for (int i = 0; i < P; i++) {
        px[i] = x; py[i] = y;
        d = w[i] ? (d + 3) & 3 : (d + 1) & 3; /* black: left, white: right */
        x += DX[d]; y += DY[d];
    }
    if (d != 0) return 0;
    int vx = x, vy = y;
    if (vx == 0 && vy == 0) return 0;
    for (int i = 0; i < P; i++) {
        int count = 0;
        for (int j = 0; j < P; j++) {
            int ex = px[j] - px[i], ey = py[j] - py[i];
            /* need pos(j) + k v = pos(i) with m = kP + j < i, i.e. ex = -k vx, ey = -k vy */
            if (ex == 0 && ey == 0) { if (j < i) count++; continue; }
            /* ex = t vx, ey = t vy with t = -k >= 1 */
            long t;
            if (vx != 0) { if (ex % vx) continue; t = ex / vx; }
            else { if (ex != 0) continue; if (ey % vy) continue; t = ey / vy; }
            if ((long)vx * t != ex || (long)vy * t != ey) continue;
            if (t >= 1) count++;
        }
        if ((count & 1) != w[i]) return 0;
    }
    *vx_out = vx; *vy_out = vy;
    return 1;
}

static int is_min_rotation(const unsigned char *w, int P) {
    for (int s = 1; s < P; s++) {
        for (int i = 0; i < P; i++) {
            unsigned char a = w[(i + s) % P], b = w[i];
            if (a < b) return 0;
            if (a > b) break;
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc >= 4) {
        const char *s = argv[3];
        int P = (int)strlen(s);
        unsigned char w[1024];
        for (int i = 0; i < P; i++) w[i] = s[i] == '1';
        int vx, vy;
        int ok = consistent(w, P, &vx, &vy);
        printf("check P=%d consistent=%d v=(%d,%d)\n", P, ok, ok ? vx : 0, ok ? vy : 0);
        return 0;
    }
    int pmin = atoi(argv[1]), pmax = atoi(argv[2]);
    for (int P = pmin; P <= pmax; P++) {
        unsigned char w[64];
        long found = 0;
        for (uint64_t code = 0; code < ((uint64_t)1 << P); code++) {
            int ones = __builtin_popcountll(code);
            if (((P - 2 * ones) % 4 + 4) % 4 != 0) continue; /* heading must return */
            for (int i = 0; i < P; i++) w[i] = (code >> i) & 1;
            int vx, vy;
            if (!consistent(w, P, &vx, &vy)) continue;
            if (!is_min_rotation(w, P)) continue;
            found++;
            printf("P=%d word=", P);
            for (int i = 0; i < P; i++) putchar('0' + w[i]);
            printf(" v=(%d,%d)\n", vx, vy);
        }
        printf("P=%d done: %ld words (up to rotation)\n", P, found);
        fflush(stdout);
    }
    return 0;
}
