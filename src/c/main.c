/**
 * PebbleGolf — Golf Card Game for Pebble
 * Targets: emery (Time 2), gabbro (Round 2)
 *
 * 2-6 player pass & play. Each player gets 4 cards (2x2 grid).
 * Top 2 start face-down. Draw from pile or discard, replace a card
 * or discard. Knock when you think you have the lowest score.
 * J=0, A=1, 2-10=face, Q/K=10. Lowest score wins.
 */

#include <pebble.h>
#include <stdlib.h>

// ============================================================================
// CONSTANTS
// ============================================================================
#define MAX_PLAYERS 6
#define HAND_SIZE   4
#define DECK_SIZE   52
#define NUM_TOKENS  6
#define P_LO_SCORE  0

// Game states
enum {
  ST_SETUP, ST_ORDER, ST_INSTRUCT, ST_REVEAL,
  ST_PLAY, ST_DRAWN, ST_BLACKOUT, ST_GAMEOVER
};

// Suits
enum { SUIT_SPADE, SUIT_HEART, SUIT_DIAMOND, SUIT_CLUB };

// ============================================================================
// TYPES
// ============================================================================
typedef struct { uint8_t rank; uint8_t suit; } Card;

typedef struct {
  Card hand[HAND_SIZE];
  bool face_up[HAND_SIZE];
  bool seen_cards;
  int  icon;
} Player;

typedef struct { Card card; int player; } LogEntry;

// ============================================================================
// STATIC DATA
// ============================================================================
static const char *s_rank_str[] = {
  "A","2","3","4","5","6","7","8","9","10","J","Q","K"
};
static const char s_suit_ch[] = {'S','H','D','C'};

// Player tokens (Font Awesome icons, same as Farkle)
static const char *s_tok_name[] = {
  "Star","Heart","Diamond","Circle","Square","Bolt"
};
static const char *s_tok_char[] = {
  "\xEF\x80\x85",  // U+F005 Star
  "\xEF\x80\x84",  // U+F004 Heart
  "\xEF\x88\x99",  // U+F219 Diamond
  "\xEF\x84\x91",  // U+F111 Circle
  "\xEF\x83\x88",  // U+F0C8 Square
  "\xEF\x83\xA7",  // U+F0E7 Bolt
};

// ============================================================================
// GLOBALS
// ============================================================================
static Window *s_win;
static Layer  *s_canvas;
static GFont   s_icon_font_20, s_icon_font_14;

// State
static int s_state = ST_SETUP;
static int s_num_players;
static int s_setup_cursor = 0;  // 0..4 => 2..6 players
static int s_cursor = 0;

// Players
static Player s_players[MAX_PLAYERS];
static int    s_order[MAX_PLAYERS];
static int    s_cur_idx;
static int    s_rounds;

// Deck
static Card s_deck[DECK_SIZE];
static int  s_deck_top, s_deck_count;

// Discard pile
static Card s_discard[DECK_SIZE];
static int  s_discard_count;

// Discard log (for history overlay)
static LogEntry s_log[DECK_SIZE];
static int  s_log_count;
static int  s_log_turn_start[MAX_PLAYERS];

// Current drawn card
static Card s_drawn_card;

// Knock tracking
static bool s_knocked;
static int  s_knocker_idx;

// Overlay toggles
static bool s_show_standings;
static bool s_show_history;

// Persistence
static int s_lo_score;

// ============================================================================
// CARD STRING HELPER
// ============================================================================
static char s_cbuf[8][6];
static int  s_cbi;

static const char *card_str(Card c) {
  char *b = s_cbuf[s_cbi++ & 7];
  snprintf(b, 6, "%s%c", s_rank_str[c.rank], s_suit_ch[c.suit]);
  return b;
}

// ============================================================================
// CARD UTILITIES
// ============================================================================
static int card_value(Card c) {
  if(c.rank == 10) return 0;       // Jack = 0
  if(c.rank == 0)  return 1;       // Ace = 1
  if(c.rank <= 9)  return c.rank + 1; // 2-10 = face value
  return 10;                        // Q, K = 10
}

static int hand_score(int pi) {
  int t = 0;
  for(int i = 0; i < HAND_SIZE; i++) t += card_value(s_players[pi].hand[i]);
  return t;
}

static void shuffle_cards(Card *arr, int n) {
  for(int i = n - 1; i > 0; i--) {
    int j = rand() % (i + 1);
    Card t = arr[i]; arr[i] = arr[j]; arr[j] = t;
  }
}

static void init_deck(void) {
  int n = 0;
  for(int s = 0; s < 4; s++)
    for(int r = 0; r < 13; r++) {
      s_deck[n].rank = r; s_deck[n].suit = s; n++;
    }
  s_deck_count = DECK_SIZE;
  s_deck_top = 0;
}

static void reshuffle_discard(void) {
  if(s_discard_count <= 1) return;
  Card top = s_discard[s_discard_count - 1];
  int n = s_discard_count - 1;
  for(int i = 0; i < n; i++) s_deck[i] = s_discard[i];
  shuffle_cards(s_deck, n);
  s_deck_top = 0;
  s_deck_count = n;
  s_discard[0] = top;
  s_discard_count = 1;
}

static Card draw_from_deck(void) {
  if(s_deck_top >= s_deck_count) reshuffle_discard();
  if(s_deck_top >= s_deck_count) return (Card){0, 0};
  return s_deck[s_deck_top++];
}

static int deck_remaining(void) { return s_deck_count - s_deck_top; }

static void push_discard(Card c) { s_discard[s_discard_count++] = c; }
static Card peek_discard(void) {
  return s_discard_count > 0 ? s_discard[s_discard_count - 1] : (Card){0, 0};
}
static Card pop_discard(void) {
  return s_discard_count > 0 ? s_discard[--s_discard_count] : (Card){0, 0};
}

static void log_discard(Card c, int player) {
  if(s_log_count < DECK_SIZE)
    s_log[s_log_count++] = (LogEntry){c, player};
}

// ============================================================================
// GAME SETUP
// ============================================================================
static int cur_player(void) { return s_order[s_cur_idx]; }

static void shuffle_order(void) {
  int icons[NUM_TOKENS];
  for(int i = 0; i < NUM_TOKENS; i++) icons[i] = i;
  for(int i = NUM_TOKENS - 1; i > 0; i--) {
    int j = rand() % (i + 1);
    int t = icons[i]; icons[i] = icons[j]; icons[j] = t;
  }
  for(int i = 0; i < s_num_players; i++) {
    s_players[i].icon = icons[i];
    s_order[i] = i;
  }
  for(int i = s_num_players - 1; i > 0; i--) {
    int j = rand() % (i + 1);
    int t = s_order[i]; s_order[i] = s_order[j]; s_order[j] = t;
  }
}

static void deal_hands(void) {
  init_deck();
  shuffle_cards(s_deck, DECK_SIZE);
  s_discard_count = 0;
  s_log_count = 0;
  for(int i = 0; i < s_num_players; i++) {
    for(int j = 0; j < HAND_SIZE; j++)
      s_players[i].hand[j] = draw_from_deck();
    s_players[i].face_up[0] = false;
    s_players[i].face_up[1] = false;
    s_players[i].face_up[2] = true;
    s_players[i].face_up[3] = true;
    s_players[i].seen_cards = false;
  }
  // Initial discard
  push_discard(draw_from_deck());
  // Set log start for all players after initial discard
  for(int i = 0; i < s_num_players; i++)
    s_log_turn_start[i] = s_log_count;
}

static void next_player(void) {
  s_cur_idx = (s_cur_idx + 1) % s_num_players;
  if(s_cur_idx == 0) s_rounds++;
}

// ============================================================================
// COLORS
// ============================================================================
#ifdef PBL_COLOR
static GColor tok_color(int t) {
  switch(t) {
    case 0: return GColorYellow;
    case 1: return GColorRed;
    case 2: return GColorCyan;
    case 3: return GColorGreen;
    case 4: return GColorOrange;
    default: return GColorPurple;
  }
}
static GColor suit_gcolor(int suit) {
  return (suit == SUIT_HEART || suit == SUIT_DIAMOND) ? GColorRed : GColorBlack;
}
#endif

// ============================================================================
// DRAWING HELPERS
// ============================================================================
static void draw_token(GContext *ctx, int cx, int cy, int icon, bool lg) {
  #ifdef PBL_COLOR
  graphics_context_set_text_color(ctx, tok_color(icon));
  #else
  graphics_context_set_text_color(ctx, GColorWhite);
  #endif
  GFont f = lg ? s_icon_font_20 : s_icon_font_14;
  int sz = lg ? 30 : 22;
  if(!f) {
    f = fonts_get_system_font(lg ? FONT_KEY_GOTHIC_24_BOLD : FONT_KEY_GOTHIC_18_BOLD);
    char nm[2] = {s_tok_name[icon][0], 0};
    graphics_draw_text(ctx, nm, f,
      GRect(cx-sz/2, cy-sz/2, sz, sz),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
    return;
  }
  graphics_draw_text(ctx, s_tok_char[icon], f,
    GRect(cx-sz/2, cy-sz/2, sz, sz),
    GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
}

static void draw_card_gfx(GContext *ctx, int x, int y, int cw, int ch,
                           Card card, bool face, bool hl) {
  if(face) {
    // White card face
    graphics_context_set_fill_color(ctx, GColorWhite);
    graphics_fill_rect(ctx, GRect(x, y, cw, ch), 3, GCornersAll);
    #ifdef PBL_COLOR
    graphics_context_set_stroke_color(ctx, hl ? GColorYellow : GColorLightGray);
    #else
    graphics_context_set_stroke_color(ctx, hl ? GColorWhite : GColorBlack);
    #endif
    graphics_context_set_stroke_width(ctx, hl ? 2 : 1);
    graphics_draw_round_rect(ctx, GRect(x, y, cw, ch), 3);

    // Rank
    #ifdef PBL_COLOR
    graphics_context_set_text_color(ctx, suit_gcolor(card.suit));
    #else
    graphics_context_set_text_color(ctx, GColorBlack);
    #endif
    graphics_draw_text(ctx, s_rank_str[card.rank],
      fonts_get_system_font(FONT_KEY_GOTHIC_18_BOLD),
      GRect(x + 1, y - 2, cw - 2, ch / 2 + 4),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);

    // Suit letter
    char sb[2] = {s_suit_ch[card.suit], 0};
    graphics_draw_text(ctx, sb,
      fonts_get_system_font(FONT_KEY_GOTHIC_14),
      GRect(x + 1, y + ch / 2 - 5, cw - 2, ch / 2 + 2),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
  } else {
    // Card back
    #ifdef PBL_COLOR
    graphics_context_set_fill_color(ctx, GColorCobaltBlue);
    #else
    graphics_context_set_fill_color(ctx, GColorDarkGray);
    #endif
    graphics_fill_rect(ctx, GRect(x, y, cw, ch), 3, GCornersAll);
    #ifdef PBL_COLOR
    graphics_context_set_stroke_color(ctx, hl ? GColorYellow : GColorOxfordBlue);
    #else
    graphics_context_set_stroke_color(ctx, hl ? GColorWhite : GColorBlack);
    #endif
    graphics_context_set_stroke_width(ctx, hl ? 2 : 1);
    graphics_draw_round_rect(ctx, GRect(x, y, cw, ch), 3);

    graphics_context_set_text_color(ctx, GColorWhite);
    graphics_draw_text(ctx, "?",
      fonts_get_system_font(FONT_KEY_GOTHIC_18_BOLD),
      GRect(x, y + 2, cw, ch - 4),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
  }
}

// Draw stacked card backs (draw pile)
static void draw_pile_gfx(GContext *ctx, int x, int y, int cw, int ch,
                           int count, bool hl) {
  if(count <= 0) return;
  #ifdef PBL_COLOR
  if(count >= 3) {
    graphics_context_set_fill_color(ctx, GColorOxfordBlue);
    graphics_fill_rect(ctx, GRect(x - 3, y - 3, cw, ch), 3, GCornersAll);
  }
  if(count >= 2) {
    graphics_context_set_fill_color(ctx, GColorDukeBlue);
    graphics_fill_rect(ctx, GRect(x - 1, y - 1, cw, ch), 3, GCornersAll);
  }
  graphics_context_set_fill_color(ctx, GColorCobaltBlue);
  #else
  graphics_context_set_fill_color(ctx, GColorDarkGray);
  #endif
  graphics_fill_rect(ctx, GRect(x, y, cw, ch), 3, GCornersAll);
  graphics_context_set_stroke_color(ctx, hl ? GColorWhite : GColorLightGray);
  graphics_context_set_stroke_width(ctx, hl ? 2 : 1);
  graphics_draw_round_rect(ctx, GRect(x, y, cw, ch), 3);

  graphics_context_set_text_color(ctx, GColorWhite);
  char buf[4];
  snprintf(buf, sizeof(buf), "%d", count);
  graphics_draw_text(ctx, buf,
    fonts_get_system_font(FONT_KEY_GOTHIC_14_BOLD),
    GRect(x, y + ch / 2 - 10, cw, 20),
    GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
}

// Draw the player header (icon + name + round)
static void draw_header(GContext *ctx, int w, int pad, int cp) {
  Player *p = &s_players[cp];
  draw_token(ctx, pad + 12, 14, p->icon, false);
  graphics_context_set_text_color(ctx, GColorWhite);
  char hdr[20];
  snprintf(hdr, sizeof(hdr), "Player %d", cp + 1);
  graphics_draw_text(ctx, hdr,
    fonts_get_system_font(FONT_KEY_GOTHIC_18_BOLD),
    GRect(pad + 26, 1, w / 2, 24),
    GTextOverflowModeTrailingEllipsis, GTextAlignmentLeft, NULL);
  char rnd[10];
  snprintf(rnd, sizeof(rnd), "Rd %d", s_rounds);
  graphics_draw_text(ctx, rnd,
    fonts_get_system_font(FONT_KEY_GOTHIC_14),
    GRect(w - pad - 48, 5, 48, 18),
    GTextOverflowModeTrailingEllipsis, GTextAlignmentRight, NULL);
}

// Draw the 2x2 hand grid; returns card_y for layout
static int draw_hand_grid(GContext *ctx, int pad, int card_y,
                          int cw, int ch, int gap, Player *p,
                          int hl_idx) {
  for(int i = 0; i < HAND_SIZE; i++) {
    int col = i % 2, row = i / 2;
    int cx = pad + 6 + col * (cw + gap);
    int cy = card_y + row * (ch + gap);
    draw_card_gfx(ctx, cx, cy, cw, ch,
      p->hand[i], p->face_up[i], i == hl_idx);
  }
  return card_y + 2 * (ch + gap);
}

// Draw a menu item
static void draw_menu_item(GContext *ctx, int x, int y, int w,
                           const char *text, bool selected) {
  GFont f = selected
    ? fonts_get_system_font(FONT_KEY_GOTHIC_18_BOLD)
    : fonts_get_system_font(FONT_KEY_GOTHIC_18);
  #ifdef PBL_COLOR
  graphics_context_set_text_color(ctx, selected ? GColorYellow : GColorLightGray);
  #else
  graphics_context_set_text_color(ctx, selected ? GColorWhite : GColorLightGray);
  #endif
  char buf[40];
  snprintf(buf, sizeof(buf), "%s %s", selected ? ">" : " ", text);
  graphics_draw_text(ctx, buf, f,
    GRect(x, y, w, 22),
    GTextOverflowModeTrailingEllipsis, GTextAlignmentLeft, NULL);
}

// ============================================================================
// CANVAS RENDERING
// ============================================================================
static void canvas_proc(Layer *l, GContext *ctx) {
  GRect b = layer_get_bounds(l);
  int w = b.size.w, h = b.size.h;
  int pad = PBL_IF_ROUND_ELSE(18, 4);

  // Background — dark green felt
  #ifdef PBL_COLOR
  graphics_context_set_fill_color(ctx, GColorFromHEX(0x004400));
  #else
  graphics_context_set_fill_color(ctx, GColorBlack);
  #endif
  graphics_fill_rect(ctx, b, 0, GCornerNone);

  GFont f_lg = fonts_get_system_font(FONT_KEY_GOTHIC_28_BOLD);
  GFont f_md = fonts_get_system_font(FONT_KEY_GOTHIC_18_BOLD);
  GFont f_sm = fonts_get_system_font(FONT_KEY_GOTHIC_14);

  int cw = 34, ch = 44, gap = 6;

  // ======== SETUP ========
  if(s_state == ST_SETUP) {
    graphics_context_set_text_color(ctx, GColorWhite);
    graphics_draw_text(ctx, "GOLF", f_lg,
      GRect(0, h * 8 / 100, w, 34),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);

    graphics_draw_text(ctx, "Card Game", f_sm,
      GRect(0, h * 8 / 100 + 30, w, 16),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);

    // Player count picker
    const char *opts[] = {"2 Players","3 Players","4 Players","5 Players","6 Players"};
    int cy = h * 42 / 100;

    #ifdef PBL_COLOR
    graphics_context_set_fill_color(ctx, GColorFromHEX(0x006600));
    #else
    graphics_context_set_fill_color(ctx, GColorWhite);
    #endif
    int mx = 40;
    graphics_fill_rect(ctx, GRect(mx, cy - 2, w - mx * 2, 30), 6, GCornersAll);
    #ifdef PBL_COLOR
    graphics_context_set_text_color(ctx, GColorWhite);
    #else
    graphics_context_set_text_color(ctx, GColorBlack);
    #endif
    graphics_draw_text(ctx, opts[s_setup_cursor], f_lg,
      GRect(0, cy - 2, w, 30),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);

    // Low score display
    graphics_context_set_text_color(ctx, GColorWhite);
    if(s_lo_score > 0) {
      char lbuf[24];
      snprintf(lbuf, sizeof(lbuf), "Best: %d pts", s_lo_score);
      #ifdef PBL_COLOR
      graphics_context_set_text_color(ctx, GColorYellow);
      #endif
      graphics_draw_text(ctx, lbuf, f_sm,
        GRect(0, cy + 34, w, 16),
        GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
      graphics_context_set_text_color(ctx, GColorWhite);
    }

    graphics_draw_text(ctx, "SELECT to start", f_sm,
      GRect(0, h * 74 / 100, w, 16),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
    graphics_draw_text(ctx, "UP/DOWN: players", f_sm,
      GRect(0, h * 82 / 100, w, 16),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
  }

  // ======== ORDER (token assignment) ========
  else if(s_state == ST_ORDER) {
    graphics_context_set_text_color(ctx, GColorWhite);
    graphics_draw_text(ctx, "Player Order", f_md,
      GRect(0, h * 8 / 100, w, 24),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);

    int gy = h * 22 / 100;
    int row_h = 26;
    int cols = (s_num_players <= 3) ? 1 : 2;
    int per_col = (s_num_players + cols - 1) / cols;
    for(int i = 0; i < s_num_players; i++) {
      int pi = s_order[i];
      int c = i / per_col, r = i % per_col;
      int col_w = w / cols;
      int tx = c * col_w + (cols == 1 ? w / 2 - 30 : col_w / 2 - 20);
      int ty = gy + r * row_h;
      char lbl[24];
      snprintf(lbl, sizeof(lbl), "%d.", i + 1);
      graphics_context_set_text_color(ctx, GColorWhite);
      graphics_draw_text(ctx, lbl, f_sm,
        GRect(tx - 14, ty + 4, 18, 18),
        GTextOverflowModeTrailingEllipsis, GTextAlignmentRight, NULL);
      draw_token(ctx, tx + 14, ty + 12, s_players[pi].icon, false);
      graphics_context_set_text_color(ctx, GColorWhite);
      graphics_draw_text(ctx, s_tok_name[s_players[pi].icon], f_sm,
        GRect(tx + 28, ty + 4, col_w / 2 + 20, 18),
        GTextOverflowModeTrailingEllipsis, GTextAlignmentLeft, NULL);
    }

    graphics_context_set_text_color(ctx, GColorWhite);
    graphics_draw_text(ctx, "SELECT to shuffle & deal", f_sm,
      GRect(0, h * 80 / 100, w, 16),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
  }

  // ======== INSTRUCT (rules overlay per player first turn) ========
  else if(s_state == ST_INSTRUCT) {
    int cp = cur_player();
    // Dark overlay
    graphics_context_set_fill_color(ctx, GColorBlack);
    graphics_fill_rect(ctx, GRect(pad, pad, w - pad * 2, h - pad * 2), 8, GCornersAll);

    int ly = pad + 6;
    // Player icon + name
    draw_token(ctx, w / 2, ly + 10, s_players[cp].icon, true);
    ly += 26;
    graphics_context_set_text_color(ctx, GColorWhite);
    char pn[20];
    snprintf(pn, sizeof(pn), "PLAYER %d", cp + 1);
    graphics_draw_text(ctx, pn, f_md,
      GRect(pad, ly, w - pad * 2, 22),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
    ly += 24;

    // Rules text
    #ifdef PBL_COLOR
    graphics_context_set_text_color(ctx, GColorYellow);
    #endif
    const char *rules[] = {
      "Memorize your top 2!",
      "",
      "J=0  A=1  2-10=#",
      "Q=10  K=10",
      "",
      "Lowest score wins.",
      "Knock when ready -",
      "others get 1 last turn."
    };
    for(int i = 0; i < 8; i++) {
      graphics_draw_text(ctx, rules[i], f_sm,
        GRect(pad + 6, ly, w - pad * 2 - 12, 16),
        GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
      ly += (rules[i][0] == 0) ? 6 : 16;
    }

    graphics_context_set_text_color(ctx, GColorWhite);
    graphics_draw_text(ctx, "SELECT to see cards", f_sm,
      GRect(pad, h - pad - 20, w - pad * 2, 18),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
  }

  // ======== REVEAL (show all 4 cards for memorization) ========
  else if(s_state == ST_REVEAL) {
    int cp = cur_player();
    Player *p = &s_players[cp];

    draw_header(ctx, w, pad, cp);

    #ifdef PBL_COLOR
    graphics_context_set_text_color(ctx, GColorYellow);
    #else
    graphics_context_set_text_color(ctx, GColorWhite);
    #endif
    graphics_draw_text(ctx, "MEMORIZE YOUR CARDS!", f_sm,
      GRect(0, 24, w, 16),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);

    // Draw all 4 cards face up (temporary reveal)
    int card_y = 44;
    int grid_w = cw * 2 + gap;
    int gx = (w - grid_w) / 2;
    for(int i = 0; i < HAND_SIZE; i++) {
      int col = i % 2, row = i / 2;
      int cx = gx + col * (cw + gap);
      int cy = card_y + row * (ch + gap);
      draw_card_gfx(ctx, cx, cy, cw, ch, p->hand[i], true,
        row == 0); // highlight top 2 (the ones that will hide)
    }

    // Labels
    graphics_context_set_text_color(ctx, GColorWhite);
    int below = card_y + 2 * (ch + gap) + 4;
    graphics_draw_text(ctx, "Top 2 will be hidden!", f_sm,
      GRect(0, below, w, 16),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
    graphics_draw_text(ctx, "SELECT when memorized", f_sm,
      GRect(0, below + 18, w, 16),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
  }

  // ======== PLAY (main game turn) ========
  else if(s_state == ST_PLAY) {
    int cp = cur_player();
    Player *p = &s_players[cp];

    draw_header(ctx, w, pad, cp);

    // Knocked warning
    int card_y = 26;
    if(s_knocked) {
      #ifdef PBL_COLOR
      graphics_context_set_text_color(ctx, GColorRed);
      #else
      graphics_context_set_text_color(ctx, GColorWhite);
      #endif
      graphics_draw_text(ctx, "LAST TURN!", f_sm,
        GRect(0, 24, w, 16),
        GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
      card_y = 40;
    }

    // Player's hand
    draw_hand_grid(ctx, pad, card_y, cw, ch, gap, p, -1);

    // Draw pile + discard on right side
    int pile_x = pad + 6 + 2 * (cw + gap) + 16;
    draw_pile_gfx(ctx, pile_x, card_y, cw, ch,
      deck_remaining(), s_cursor == 0);

    if(s_discard_count > 0) {
      draw_card_gfx(ctx, pile_x, card_y + ch + gap, cw, ch,
        peek_discard(), true, s_cursor == 1);
    }

    // Recent discards hint (show last 2-3 under discard)
    if(s_discard_count > 1) {
      graphics_context_set_text_color(ctx, GColorLightGray);
      int disc_y = card_y + 2 * (ch + gap) + 2;
      int show = s_discard_count - 1;
      if(show > 3) show = 3;
      for(int i = 0; i < show; i++) {
        int idx = s_discard_count - 2 - i;
        if(idx < 0) break;
        graphics_draw_text(ctx, card_str(s_discard[idx]), f_sm,
          GRect(pile_x, disc_y + i * 14, cw, 14),
          GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
      }
    }

    // Menu
    int menu_y = card_y + 2 * (ch + gap) + 8;
    char draw_str[24], disc_str[24];
    snprintf(draw_str, sizeof(draw_str), "Draw (%d left)", deck_remaining());
    snprintf(disc_str, sizeof(disc_str), "Take %s", card_str(peek_discard()));

    draw_menu_item(ctx, pad + 2, menu_y, w - pad * 2, draw_str, s_cursor == 0);
    draw_menu_item(ctx, pad + 2, menu_y + 22, w - pad * 2, disc_str, s_cursor == 1);
    if(!s_knocked) {
      draw_menu_item(ctx, pad + 2, menu_y + 44, w - pad * 2, "Knock", s_cursor == 2);
    }

    // Hints
    graphics_context_set_text_color(ctx, GColorLightGray);
    graphics_draw_text(ctx, "Hold UP:standings  DOWN:history", f_sm,
      GRect(0, h - 16, w, 14),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
  }

  // ======== DRAWN (after drawing, choose replacement) ========
  else if(s_state == ST_DRAWN) {
    int cp = cur_player();
    Player *p = &s_players[cp];

    // Header with drawn card info
    draw_token(ctx, pad + 12, 14, p->icon, false);
    graphics_context_set_text_color(ctx, GColorWhite);
    char dstr[20];
    snprintf(dstr, sizeof(dstr), "Drew: %s", card_str(s_drawn_card));
    graphics_draw_text(ctx, dstr, f_md,
      GRect(pad + 26, 1, w - pad - 30, 24),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentLeft, NULL);

    // Drawn card preview (small, top-right)
    draw_card_gfx(ctx, w - pad - cw - 4, 0, cw - 4, ch - 8,
      s_drawn_card, true, false);

    // Player's hand with highlight on cursor
    int card_y = 28;
    draw_hand_grid(ctx, pad, card_y, cw, ch, gap, p,
      s_cursor < HAND_SIZE ? s_cursor : -1);

    // Value label for card scoring
    #ifdef PBL_COLOR
    graphics_context_set_text_color(ctx, GColorYellow);
    #else
    graphics_context_set_text_color(ctx, GColorWhite);
    #endif
    char val_str[24];
    snprintf(val_str, sizeof(val_str), "Drew %s (val: %d)",
      card_str(s_drawn_card), card_value(s_drawn_card));
    int info_y = card_y + 2 * (ch + gap) + 2;
    graphics_draw_text(ctx, val_str, f_sm,
      GRect(pad, info_y, w - pad * 2, 16),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);

    // Replacement menu
    int menu_y = info_y + 20;
    const char *pos_names[] = {"Top-L", "Top-R", "Bot-L", "Bot-R"};
    for(int i = 0; i < HAND_SIZE; i++) {
      char item[32];
      if(p->face_up[i])
        snprintf(item, sizeof(item), "%s (%s)", pos_names[i],
          card_str(p->hand[i]));
      else
        snprintf(item, sizeof(item), "%s (??)", pos_names[i]);
      draw_menu_item(ctx, pad + 2, menu_y + i * 20, w - pad * 2,
        item, s_cursor == i);
    }
    char disc_item[24];
    snprintf(disc_item, sizeof(disc_item), "Discard %s",
      card_str(s_drawn_card));
    draw_menu_item(ctx, pad + 2, menu_y + HAND_SIZE * 20, w - pad * 2,
      disc_item, s_cursor == HAND_SIZE);
  }

  // ======== BLACKOUT (pass to next player) ========
  else if(s_state == ST_BLACKOUT) {
    int cp = cur_player();
    graphics_context_set_fill_color(ctx, GColorBlack);
    graphics_fill_rect(ctx, b, 0, GCornerNone);

    int cy = h / 2 - 40;
    graphics_context_set_text_color(ctx, GColorWhite);
    graphics_draw_text(ctx, "Pass watch to", f_sm,
      GRect(0, cy, w, 16),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);

    draw_token(ctx, w / 2, cy + 36, s_players[cp].icon, true);

    char pn[20];
    snprintf(pn, sizeof(pn), "PLAYER %d", cp + 1);
    #ifdef PBL_COLOR
    graphics_context_set_text_color(ctx, tok_color(s_players[cp].icon));
    #endif
    graphics_draw_text(ctx, pn, f_lg,
      GRect(0, cy + 50, w, 32),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);

    graphics_context_set_text_color(ctx, GColorWhite);
    graphics_draw_text(ctx, "SELECT when ready", f_sm,
      GRect(0, h - 30, w, 16),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
  }

  // ======== GAMEOVER ========
  else if(s_state == ST_GAMEOVER) {
    #ifdef PBL_COLOR
    graphics_context_set_text_color(ctx, GColorYellow);
    #else
    graphics_context_set_text_color(ctx, GColorWhite);
    #endif
    graphics_draw_text(ctx, "GAME OVER!", f_lg,
      GRect(0, pad, w, 32),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);

    // Calculate scores and find winner
    int scores[MAX_PLAYERS];
    int lo = 999;
    for(int i = 0; i < s_num_players; i++) {
      scores[i] = hand_score(i);
      if(scores[i] < lo) lo = scores[i];
    }

    // Display each player
    int ly = pad + 34;
    int row_h = (s_num_players <= 4) ? 28 : 22;
    GFont rf = (s_num_players <= 4) ? f_md : f_sm;
    GFont rf_b = (s_num_players <= 4) ? f_md : f_sm;

    for(int i = 0; i < s_num_players; i++) {
      int pi = s_order[i];
      bool winner = (scores[pi] == lo);
      draw_token(ctx, pad + 12, ly + row_h / 2, s_players[pi].icon, false);

      // Cards as compact text
      char cards[24];
      snprintf(cards, sizeof(cards), "%s %s %s %s",
        card_str(s_players[pi].hand[0]),
        card_str(s_players[pi].hand[1]),
        card_str(s_players[pi].hand[2]),
        card_str(s_players[pi].hand[3]));

      char line[48];
      if(winner)
        snprintf(line, sizeof(line), "P%d: %s =%d WIN", pi + 1, cards, scores[pi]);
      else
        snprintf(line, sizeof(line), "P%d: %s =%d", pi + 1, cards, scores[pi]);

      #ifdef PBL_COLOR
      graphics_context_set_text_color(ctx,
        winner ? GColorYellow : GColorWhite);
      #else
      graphics_context_set_text_color(ctx, GColorWhite);
      #endif
      graphics_draw_text(ctx, line, winner ? rf_b : rf,
        GRect(pad + 24, ly + 2, w - pad * 2 - 28, row_h),
        GTextOverflowModeTrailingEllipsis, GTextAlignmentLeft, NULL);

      ly += row_h;
    }

    graphics_context_set_text_color(ctx, GColorWhite);
    graphics_draw_text(ctx, "SELECT: new game", f_sm,
      GRect(0, h - 18, w, 16),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
  }

  // ======== OVERLAYS ========

  // Standings (hold UP)
  if(s_show_standings && s_state >= ST_PLAY && s_state <= ST_DRAWN) {
    graphics_context_set_fill_color(ctx, GColorBlack);
    int op = pad + 8;
    graphics_fill_rect(ctx, GRect(op, op, w - op * 2, h - op * 2), 8, GCornersAll);

    int ly = op + 6;
    graphics_context_set_text_color(ctx, GColorWhite);
    graphics_draw_text(ctx, "STANDINGS", f_md,
      GRect(op, ly, w - op * 2, 22),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
    ly += 26;

    for(int i = 0; i < s_num_players; i++) {
      int pi = s_order[i];
      bool cur = (i == s_cur_idx);
      Player *p = &s_players[pi];
      draw_token(ctx, op + 14, ly + 10, p->icon, false);

      // Show visible cards
      char vis[20] = "";
      for(int j = 0; j < HAND_SIZE; j++) {
        if(p->face_up[j]) {
          char tmp[6];
          snprintf(tmp, sizeof(tmp), "%s ", card_str(p->hand[j]));
          strncat(vis, tmp, sizeof(vis) - strlen(vis) - 1);
        } else {
          strncat(vis, "__ ", sizeof(vis) - strlen(vis) - 1);
        }
      }

      #ifdef PBL_COLOR
      graphics_context_set_text_color(ctx, cur ? GColorYellow : GColorWhite);
      #endif
      graphics_draw_text(ctx, vis, cur ? f_md : f_sm,
        GRect(op + 28, ly + 2, w - op * 2 - 36, 20),
        GTextOverflowModeTrailingEllipsis, GTextAlignmentLeft, NULL);
      ly += 22;
    }
  }

  // History (hold DOWN)
  if(s_show_history && s_state >= ST_PLAY && s_state <= ST_DRAWN) {
    graphics_context_set_fill_color(ctx, GColorBlack);
    int op = pad + 8;
    graphics_fill_rect(ctx, GRect(op, op, w - op * 2, h - op * 2), 8, GCornersAll);

    int ly = op + 6;
    #ifdef PBL_COLOR
    graphics_context_set_text_color(ctx, GColorYellow);
    #else
    graphics_context_set_text_color(ctx, GColorWhite);
    #endif
    graphics_draw_text(ctx, "SINCE YOUR TURN", f_md,
      GRect(op, ly, w - op * 2, 22),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
    ly += 26;

    int cp = cur_player();
    int start = s_log_turn_start[cp];
    int shown = 0;
    for(int i = start; i < s_log_count && shown < 8; i++) {
      LogEntry *e = &s_log[i];
      char line[32];
      if(e->player >= 0)
        snprintf(line, sizeof(line), "P%d: %s", e->player + 1,
          card_str(e->card));
      else
        snprintf(line, sizeof(line), "Dealt: %s", card_str(e->card));

      graphics_context_set_text_color(ctx, GColorWhite);
      if(e->player >= 0)
        draw_token(ctx, op + 12, ly + 8, s_players[e->player].icon, false);
      graphics_draw_text(ctx, line, f_sm,
        GRect(op + 24, ly, w - op * 2 - 28, 18),
        GTextOverflowModeTrailingEllipsis, GTextAlignmentLeft, NULL);
      ly += 18;
      shown++;
    }

    if(shown == 0) {
      graphics_context_set_text_color(ctx, GColorLightGray);
      graphics_draw_text(ctx, "Nothing yet!", f_sm,
        GRect(op, ly, w - op * 2, 18),
        GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
    }
  }
}

// ============================================================================
// TRANSITION HELPER
// ============================================================================
static void goto_next(void) {
  int cp = cur_player();
  // Mark this player's log position
  s_log_turn_start[cp] = s_log_count;
  // Advance
  next_player();
  if(s_knocked && s_cur_idx == s_knocker_idx) {
    // Everyone else has had their last turn
    s_state = ST_GAMEOVER;
    // Save low score
    int lo = 999;
    for(int i = 0; i < s_num_players; i++) {
      int sc = hand_score(i);
      if(sc < lo) lo = sc;
    }
    if(s_lo_score == 0 || lo < s_lo_score) {
      s_lo_score = lo;
      persist_write_int(P_LO_SCORE, s_lo_score);
    }
  } else {
    s_state = ST_BLACKOUT;
  }
}

// ============================================================================
// BUTTON HANDLERS
// ============================================================================
static void select_click(ClickRecognizerRef ref, void *ctx) {
  if(s_state == ST_SETUP) {
    s_num_players = s_setup_cursor + 2;
    shuffle_order();
    s_state = ST_ORDER;
  }
  else if(s_state == ST_ORDER) {
    shuffle_order();
    deal_hands();
    s_cur_idx = 0;
    s_rounds = 1;
    s_knocked = false;
    s_state = ST_INSTRUCT;
  }
  else if(s_state == ST_INSTRUCT) {
    s_state = ST_REVEAL;
  }
  else if(s_state == ST_REVEAL) {
    s_players[cur_player()].seen_cards = true;
    s_cursor = 0;
    s_state = ST_PLAY;
  }
  else if(s_state == ST_PLAY) {
    if(s_cursor == 0) {
      // Draw from pile
      s_drawn_card = draw_from_deck();
      s_cursor = 0;
      s_state = ST_DRAWN;
    } else if(s_cursor == 1) {
      // Take from discard
      s_drawn_card = pop_discard();
      s_cursor = 0;
      s_state = ST_DRAWN;
    } else if(s_cursor == 2 && !s_knocked) {
      // Knock
      s_knocked = true;
      s_knocker_idx = s_cur_idx;
      vibes_short_pulse();
      goto_next();
    }
  }
  else if(s_state == ST_DRAWN) {
    int cp = cur_player();
    if(s_cursor < HAND_SIZE) {
      // Replace card
      Card old = s_players[cp].hand[s_cursor];
      s_players[cp].hand[s_cursor] = s_drawn_card;
      s_players[cp].face_up[s_cursor] = true;
      push_discard(old);
      log_discard(old, cp);
    } else {
      // Discard drawn card
      push_discard(s_drawn_card);
      log_discard(s_drawn_card, cp);
    }
    goto_next();
  }
  else if(s_state == ST_BLACKOUT) {
    int cp = cur_player();
    if(!s_players[cp].seen_cards) {
      s_state = ST_INSTRUCT;
    } else {
      s_cursor = 0;
      s_log_turn_start[cp] = s_log_count;
      s_state = ST_PLAY;
    }
  }
  else if(s_state == ST_GAMEOVER) {
    s_state = ST_SETUP;
    s_setup_cursor = s_num_players - 2;
  }
  if(s_canvas) layer_mark_dirty(s_canvas);
}

static void up_click(ClickRecognizerRef ref, void *ctx) {
  if(s_state == ST_SETUP) {
    s_setup_cursor = (s_setup_cursor + 4) % 5;
  } else if(s_state == ST_PLAY) {
    int max = s_knocked ? 1 : 2;
    s_cursor = (s_cursor + max) % (max + 1);
  } else if(s_state == ST_DRAWN) {
    s_cursor = (s_cursor + HAND_SIZE) % (HAND_SIZE + 1);
  }
  if(s_canvas) layer_mark_dirty(s_canvas);
}

static void down_click(ClickRecognizerRef ref, void *ctx) {
  if(s_state == ST_SETUP) {
    s_setup_cursor = (s_setup_cursor + 1) % 5;
  } else if(s_state == ST_PLAY) {
    int max = s_knocked ? 1 : 2;
    s_cursor = (s_cursor + 1) % (max + 1);
  } else if(s_state == ST_DRAWN) {
    s_cursor = (s_cursor + 1) % (HAND_SIZE + 1);
  }
  if(s_canvas) layer_mark_dirty(s_canvas);
}

static void back_click(ClickRecognizerRef ref, void *ctx) {
  if(s_state == ST_SETUP || s_state == ST_GAMEOVER) {
    window_stack_pop(true);
  } else {
    // Back to setup (abandon game)
    s_state = ST_SETUP;
    s_setup_cursor = 0;
    if(s_canvas) layer_mark_dirty(s_canvas);
  }
}

// Hold UP = standings overlay
static void up_long_down(ClickRecognizerRef ref, void *ctx) {
  s_show_standings = true;
  if(s_canvas) layer_mark_dirty(s_canvas);
}
static void up_long_up(ClickRecognizerRef ref, void *ctx) {
  s_show_standings = false;
  if(s_canvas) layer_mark_dirty(s_canvas);
}

// Hold DOWN = history overlay
static void down_long_down(ClickRecognizerRef ref, void *ctx) {
  s_show_history = true;
  if(s_canvas) layer_mark_dirty(s_canvas);
}
static void down_long_up(ClickRecognizerRef ref, void *ctx) {
  s_show_history = false;
  if(s_canvas) layer_mark_dirty(s_canvas);
}

static void click_config(void *ctx) {
  window_single_click_subscribe(BUTTON_ID_SELECT, select_click);
  window_single_click_subscribe(BUTTON_ID_UP, up_click);
  window_single_click_subscribe(BUTTON_ID_DOWN, down_click);
  window_single_click_subscribe(BUTTON_ID_BACK, back_click);
  window_long_click_subscribe(BUTTON_ID_UP, 500, up_long_down, up_long_up);
  window_long_click_subscribe(BUTTON_ID_DOWN, 500, down_long_down, down_long_up);
}

// ============================================================================
// WINDOW
// ============================================================================
static void win_load(Window *w) {
  Layer *wl = window_get_root_layer(w);
  GRect b = layer_get_bounds(wl);
  s_canvas = layer_create(b);
  layer_set_update_proc(s_canvas, canvas_proc);
  layer_add_child(wl, s_canvas);
  window_set_click_config_provider(w, click_config);
  s_state = ST_SETUP;
  s_setup_cursor = 0;
}

static void win_unload(Window *w) {
  if(s_canvas) { layer_destroy(s_canvas); s_canvas = NULL; }
}

// ============================================================================
// LIFECYCLE
// ============================================================================
static void init(void) {
  srand(time(NULL));
  if(persist_exists(P_LO_SCORE)) s_lo_score = persist_read_int(P_LO_SCORE);
  s_icon_font_20 = fonts_load_custom_font(
    resource_get_handle(RESOURCE_ID_ICON_FONT_20));
  s_icon_font_14 = fonts_load_custom_font(
    resource_get_handle(RESOURCE_ID_ICON_FONT_14));
  s_win = window_create();
  window_set_background_color(s_win, GColorBlack);
  window_set_window_handlers(s_win, (WindowHandlers){
    .load = win_load, .unload = win_unload
  });
  window_stack_push(s_win, true);
}

static void deinit(void) {
  window_destroy(s_win);
  fonts_unload_custom_font(s_icon_font_20);
  fonts_unload_custom_font(s_icon_font_14);
}

int main(void) { init(); app_event_loop(); deinit(); return 0; }
