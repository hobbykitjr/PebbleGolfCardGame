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

#define MAX_PLAYERS 6
#define HAND_SIZE   4
#define DECK_SIZE   52
#define NUM_TOKENS  6
#define P_LO_SCORE  0

enum {
  ST_SETUP, ST_ORDER, ST_INSTRUCT, ST_REVEAL,
  ST_PLAY, ST_DRAWN, ST_BLACKOUT, ST_GAMEOVER
};

enum { SUIT_SPADE, SUIT_HEART, SUIT_DIAMOND, SUIT_CLUB };

typedef struct { uint8_t rank; uint8_t suit; } Card;

typedef struct {
  Card hand[HAND_SIZE];
  bool face_up[HAND_SIZE];
  bool temp_vis[HAND_SIZE]; // temporarily visible in standings (1 turn)
  bool seen_cards;
  int  icon;
} Player;

typedef struct { Card card; int player; } LogEntry;

static const char *s_rank_str[] = {
  "A","2","3","4","5","6","7","8","9","10","J","Q","K"
};
static const char s_suit_ch[] = {'S','H','D','C'};

static const char *s_tok_name[] = {
  "Star","Heart","Diamond","Circle","Square","Bolt"
};
static const char *s_tok_char[] = {
  "\xEF\x80\x85","\xEF\x80\x84","\xEF\x88\x99",
  "\xEF\x84\x91","\xEF\x83\x88","\xEF\x83\xA7",
};

// ============================================================================
// GLOBALS
// ============================================================================
static Window *s_win;
static Layer  *s_canvas;
static GFont   s_icon_font_20, s_icon_font_14;

static int s_state = ST_SETUP;
static int s_num_players;
static int s_setup_cursor = 0;
static int s_cursor = 0;

static Player s_players[MAX_PLAYERS];
static int    s_order[MAX_PLAYERS];
static int    s_cur_idx;
static int    s_rounds;

static Card s_deck[DECK_SIZE];
static int  s_deck_top, s_deck_count;

static Card s_discard[DECK_SIZE];
static int  s_discard_count;

static LogEntry s_log[DECK_SIZE];
static int  s_log_count;
static int  s_log_turn_start[MAX_PLAYERS];

static Card s_drawn_card;
static bool s_drew_from_discard;

static bool s_knocked;
static int  s_knocker_idx;

// Temp visibility tracking (discard-sourced replacements visible for 1 turn)
static bool s_has_temp_vis;
static int  s_temp_vis_clear_at; // player index that triggers clearing

static bool s_show_standings;
static bool s_show_history;

static int s_lo_score;

// ============================================================================
// CARD HELPERS
// ============================================================================
static char s_cbuf[8][6];
static int  s_cbi;
static const char *card_str(Card c) {
  char *b = s_cbuf[s_cbi++ & 7];
  snprintf(b, 6, "%s%c", s_rank_str[c.rank], s_suit_ch[c.suit]);
  return b;
}

static int card_value(Card c) {
  if(c.rank == 10) return 0;
  if(c.rank == 0)  return 1;
  if(c.rank <= 9)  return c.rank + 1;
  return 10;
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
  s_deck_count = DECK_SIZE; s_deck_top = 0;
}

static void reshuffle_discard(void) {
  if(s_discard_count <= 1) return;
  Card top = s_discard[s_discard_count - 1];
  int n = s_discard_count - 1;
  for(int i = 0; i < n; i++) s_deck[i] = s_discard[i];
  shuffle_cards(s_deck, n);
  s_deck_top = 0; s_deck_count = n;
  s_discard[0] = top; s_discard_count = 1;
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
  if(s_log_count < DECK_SIZE) s_log[s_log_count++] = (LogEntry){c, player};
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
  s_discard_count = 0; s_log_count = 0;
  for(int i = 0; i < s_num_players; i++) {
    for(int j = 0; j < HAND_SIZE; j++)
      s_players[i].hand[j] = draw_from_deck();
    s_players[i].face_up[0] = false;
    s_players[i].face_up[1] = false;
    s_players[i].face_up[2] = true;
    s_players[i].face_up[3] = true;
    for(int j = 0; j < HAND_SIZE; j++) s_players[i].temp_vis[j] = false;
    s_players[i].seen_cards = false;
  }
  push_discard(draw_from_deck());
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
    graphics_draw_text(ctx, nm, f, GRect(cx-sz/2, cy-sz/2, sz, sz),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
    return;
  }
  graphics_draw_text(ctx, s_tok_char[icon], f, GRect(cx-sz/2, cy-sz/2, sz, sz),
    GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
}

// Suit icon as small pixel-art shape
static void draw_suit_icon(GContext *ctx, int cx, int cy, int suit) {
  #ifdef PBL_COLOR
  graphics_context_set_fill_color(ctx, suit_gcolor(suit));
  #else
  graphics_context_set_fill_color(ctx, GColorBlack);
  #endif
  switch(suit) {
    case SUIT_HEART:
      graphics_fill_circle(ctx, GPoint(cx-2, cy-1), 2);
      graphics_fill_circle(ctx, GPoint(cx+2, cy-1), 2);
      for(int i=0;i<4;i++){int hw=3-i; if(hw>=0)
        graphics_fill_rect(ctx,GRect(cx-hw,cy+i,hw*2+1,1),0,GCornerNone);}
      break;
    case SUIT_DIAMOND:
      for(int i=-3;i<=3;i++){int hw=3-(i<0?-i:i);
        graphics_fill_rect(ctx,GRect(cx-hw,cy+i,hw*2+1,1),0,GCornerNone);}
      break;
    case SUIT_SPADE:
      for(int i=0;i<4;i++)
        graphics_fill_rect(ctx,GRect(cx-i,cy-3+i,i*2+1,1),0,GCornerNone);
      graphics_fill_circle(ctx, GPoint(cx-2, cy+2), 2);
      graphics_fill_circle(ctx, GPoint(cx+2, cy+2), 2);
      graphics_fill_rect(ctx, GRect(cx, cy+3, 1, 2), 0, GCornerNone);
      break;
    case SUIT_CLUB:
      graphics_fill_circle(ctx, GPoint(cx, cy-2), 2);
      graphics_fill_circle(ctx, GPoint(cx-3, cy+1), 2);
      graphics_fill_circle(ctx, GPoint(cx+3, cy+1), 2);
      graphics_fill_rect(ctx, GRect(cx, cy+2, 1, 3), 0, GCornerNone);
      break;
  }
}

// Standard card (34x44)
static void draw_card_gfx(GContext *ctx, int x, int y, int cw, int ch,
                           Card card, bool face, bool hl) {
  if(face) {
    graphics_context_set_fill_color(ctx, GColorWhite);
    graphics_fill_rect(ctx, GRect(x,y,cw,ch), 3, GCornersAll);
    #ifdef PBL_COLOR
    graphics_context_set_stroke_color(ctx, hl ? GColorYellow : GColorLightGray);
    #else
    graphics_context_set_stroke_color(ctx, hl ? GColorWhite : GColorBlack);
    #endif
    graphics_context_set_stroke_width(ctx, hl ? 2 : 1);
    graphics_draw_round_rect(ctx, GRect(x,y,cw,ch), 3);
    #ifdef PBL_COLOR
    graphics_context_set_text_color(ctx, suit_gcolor(card.suit));
    #else
    graphics_context_set_text_color(ctx, GColorBlack);
    #endif
    graphics_draw_text(ctx, s_rank_str[card.rank],
      fonts_get_system_font(FONT_KEY_GOTHIC_18_BOLD),
      GRect(x+1, y-2, cw-2, ch/2+4),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
    draw_suit_icon(ctx, x + cw/2, y + ch*3/4, card.suit);
  } else {
    #ifdef PBL_COLOR
    graphics_context_set_fill_color(ctx, GColorCobaltBlue);
    #else
    graphics_context_set_fill_color(ctx, GColorDarkGray);
    #endif
    graphics_fill_rect(ctx, GRect(x,y,cw,ch), 3, GCornersAll);
    #ifdef PBL_COLOR
    graphics_context_set_stroke_color(ctx, hl ? GColorYellow : GColorOxfordBlue);
    #else
    graphics_context_set_stroke_color(ctx, hl ? GColorWhite : GColorBlack);
    #endif
    graphics_context_set_stroke_width(ctx, hl ? 2 : 1);
    graphics_draw_round_rect(ctx, GRect(x,y,cw,ch), 3);
    graphics_context_set_text_color(ctx, GColorWhite);
    graphics_draw_text(ctx, "?", fonts_get_system_font(FONT_KEY_GOTHIC_18_BOLD),
      GRect(x, y+2, cw, ch-4),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
  }
}

// Mini card for overlays (20x26)
static void draw_mini_card(GContext *ctx, int x, int y, Card card, bool face) {
  int mcw = 20, mch = 26;
  if(face) {
    graphics_context_set_fill_color(ctx, GColorWhite);
    graphics_fill_rect(ctx, GRect(x,y,mcw,mch), 2, GCornersAll);
    graphics_context_set_stroke_color(ctx, GColorLightGray);
    graphics_context_set_stroke_width(ctx, 1);
    graphics_draw_round_rect(ctx, GRect(x,y,mcw,mch), 2);
    #ifdef PBL_COLOR
    graphics_context_set_text_color(ctx, suit_gcolor(card.suit));
    #else
    graphics_context_set_text_color(ctx, GColorBlack);
    #endif
    graphics_draw_text(ctx, s_rank_str[card.rank],
      fonts_get_system_font(FONT_KEY_GOTHIC_14_BOLD),
      GRect(x, y-1, mcw, 16),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
    draw_suit_icon(ctx, x + mcw/2, y + mch - 7, card.suit);
  } else {
    #ifdef PBL_COLOR
    graphics_context_set_fill_color(ctx, GColorCobaltBlue);
    #else
    graphics_context_set_fill_color(ctx, GColorDarkGray);
    #endif
    graphics_fill_rect(ctx, GRect(x,y,mcw,mch), 2, GCornersAll);
    graphics_context_set_text_color(ctx, GColorWhite);
    graphics_draw_text(ctx, "?", fonts_get_system_font(FONT_KEY_GOTHIC_14_BOLD),
      GRect(x, y+2, mcw, 18),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
  }
}

// Draw pile (stacked card backs with count)
static void draw_pile_gfx(GContext *ctx, int x, int y, int cw, int ch,
                           int count, bool hl) {
  if(count <= 0) return;
  #ifdef PBL_COLOR
  if(count >= 3) {
    graphics_context_set_fill_color(ctx, GColorOxfordBlue);
    graphics_fill_rect(ctx, GRect(x-3,y-3,cw,ch), 3, GCornersAll);
  }
  if(count >= 2) {
    graphics_context_set_fill_color(ctx, GColorDukeBlue);
    graphics_fill_rect(ctx, GRect(x-1,y-1,cw,ch), 3, GCornersAll);
  }
  graphics_context_set_fill_color(ctx, GColorCobaltBlue);
  #else
  graphics_context_set_fill_color(ctx, GColorDarkGray);
  #endif
  graphics_fill_rect(ctx, GRect(x,y,cw,ch), 3, GCornersAll);
  graphics_context_set_stroke_color(ctx, hl ? GColorWhite : GColorLightGray);
  graphics_context_set_stroke_width(ctx, hl ? 2 : 1);
  graphics_draw_round_rect(ctx, GRect(x,y,cw,ch), 3);
  graphics_context_set_text_color(ctx, GColorWhite);
  char buf[8]; snprintf(buf, sizeof(buf), "%d", count);
  graphics_draw_text(ctx, buf, fonts_get_system_font(FONT_KEY_GOTHIC_14_BOLD),
    GRect(x, y+ch/2-10, cw, 20),
    GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
}

// Solitaire-style cascaded discard pile
static void draw_discard_cascade(GContext *ctx, int x, int y, int cw, int ch,
                                  int max_show, bool hl_top) {
  if(s_discard_count <= 0) return;
  int n = s_discard_count;
  if(n > max_show) n = max_show;
  int offset = 14;
  int start = s_discard_count - n;
  for(int i = 0; i < n; i++) {
    bool is_top = (i == n - 1);
    draw_card_gfx(ctx, x, y + i * offset, cw, ch,
      s_discard[start + i], true, is_top && hl_top);
  }
}

// ============================================================================
// CANVAS RENDERING
// ============================================================================
static void canvas_proc(Layer *l, GContext *ctx) {
  GRect b = layer_get_bounds(l);
  int w = b.size.w, h = b.size.h;
  int pad = PBL_IF_ROUND_ELSE(18, 4);

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
      GRect(0, h*8/100, w, 34),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
    graphics_draw_text(ctx, "Card Game", f_sm,
      GRect(0, h*8/100+30, w, 16),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);

    const char *opts[]={"2 Players","3 Players","4 Players","5 Players","6 Players"};
    int cy = h * 42 / 100;

    // Up arrow above
    graphics_context_set_text_color(ctx, GColorLightGray);
    if(s_icon_font_20)
      graphics_draw_text(ctx, "\xEF\x83\x98", s_icon_font_20,
        GRect(w/2-15, cy-28, 30, 26),
        GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);

    #ifdef PBL_COLOR
    graphics_context_set_fill_color(ctx, GColorFromHEX(0x006600));
    #else
    graphics_context_set_fill_color(ctx, GColorWhite);
    #endif
    graphics_fill_rect(ctx, GRect(40, cy-2, w-80, 30), 6, GCornersAll);
    #ifdef PBL_COLOR
    graphics_context_set_text_color(ctx, GColorWhite);
    #else
    graphics_context_set_text_color(ctx, GColorBlack);
    #endif
    graphics_draw_text(ctx, opts[s_setup_cursor], f_lg,
      GRect(0, cy-2, w, 30),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);

    // Down arrow below
    graphics_context_set_text_color(ctx, GColorLightGray);
    if(s_icon_font_20)
      graphics_draw_text(ctx, "\xEF\x83\x97", s_icon_font_20,
        GRect(w/2-15, cy+30, 30, 26),
        GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);

    graphics_context_set_text_color(ctx, GColorWhite);
    if(s_lo_score > 0) {
      char lbuf[24]; snprintf(lbuf, sizeof(lbuf), "Best: %d pts", s_lo_score);
      #ifdef PBL_COLOR
      graphics_context_set_text_color(ctx, GColorYellow);
      #endif
      graphics_draw_text(ctx, lbuf, f_sm,
        GRect(0, cy+58, w, 16),
        GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
      graphics_context_set_text_color(ctx, GColorWhite);
    }
    graphics_draw_text(ctx, "SELECT to start", f_sm,
      GRect(0, h*78/100, w, 16),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
  }

  // ======== ORDER (icon grid, no numbers) ========
  else if(s_state == ST_ORDER) {
    graphics_context_set_text_color(ctx, GColorWhite);
    int title_y = PBL_IF_ROUND_ELSE(pad + 8, pad + 2);
    graphics_draw_text(ctx, "Players", f_lg,
      GRect(0, title_y, w, 34),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);

    // 2-column icon grid, big icons
    int cols = 2;
    int rows = (s_num_players + 1) / 2;
    int cell_w = (w - pad * 2) / cols;
    int cell_h = 50;
    int grid_h = rows * cell_h;
    int grid_y = title_y + 36;
    // Center grid vertically in available space
    int avail = h - grid_y - 50;
    if(grid_h < avail) grid_y += (avail - grid_h) / 2;

    for(int i = 0; i < s_num_players; i++) {
      int pi = s_order[i];
      int col = i % cols, row = i / cols;
      int cx = pad + col * cell_w + cell_w / 2;
      int cy = grid_y + row * cell_h + 18;
      draw_token(ctx, cx, cy, s_players[pi].icon, true);
      graphics_context_set_text_color(ctx, GColorWhite);
      graphics_draw_text(ctx, s_tok_name[s_players[pi].icon], f_sm,
        GRect(cx - cell_w/2, cy + 16, cell_w, 16),
        GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
    }

    graphics_context_set_text_color(ctx, GColorLightGray);
    graphics_draw_text(ctx, "Everyone choose a symbol", f_sm,
      GRect(0, h - PBL_IF_ROUND_ELSE(42, 34), w, 16),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
    graphics_context_set_text_color(ctx, GColorWhite);
    graphics_draw_text(ctx, "SELECT to deal", f_sm,
      GRect(0, h - PBL_IF_ROUND_ELSE(26, 18), w, 16),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
  }

  // ======== INSTRUCT ========
  else if(s_state == ST_INSTRUCT) {
    int cp = cur_player();
    graphics_context_set_fill_color(ctx, GColorBlack);
    graphics_fill_rect(ctx, GRect(pad, pad, w-pad*2, h-pad*2), 8, GCornersAll);

    int ly = pad + 6;
    draw_token(ctx, w/2, ly+12, s_players[cp].icon, true);
    ly += 28;
    #ifdef PBL_COLOR
    graphics_context_set_text_color(ctx, tok_color(s_players[cp].icon));
    #else
    graphics_context_set_text_color(ctx, GColorWhite);
    #endif
    graphics_draw_text(ctx, s_tok_name[s_players[cp].icon], f_md,
      GRect(pad, ly, w-pad*2, 22),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
    ly += 24;

    #ifdef PBL_COLOR
    graphics_context_set_text_color(ctx, GColorYellow);
    #else
    graphics_context_set_text_color(ctx, GColorWhite);
    #endif
    const char *rules[] = {
      "Memorize your top 2!", "",
      "J=0  A=1  2-10=#", "Q=10  K=10", "",
      "Lowest score wins.", "Knock when ready -",
      "others get 1 last turn."
    };
    for(int i = 0; i < 8; i++) {
      graphics_draw_text(ctx, rules[i], f_sm,
        GRect(pad+6, ly, w-pad*2-12, 16),
        GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
      ly += (rules[i][0] == 0) ? 6 : 16;
    }
    graphics_context_set_text_color(ctx, GColorWhite);
    graphics_draw_text(ctx, "SELECT to see cards", f_sm,
      GRect(pad, h-pad-20, w-pad*2, 18),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
  }

  // ======== REVEAL ========
  else if(s_state == ST_REVEAL) {
    int cp = cur_player();
    Player *p = &s_players[cp];
    int icon_y = PBL_IF_ROUND_ELSE(32, 18);
    draw_token(ctx, w/2, icon_y, s_players[cp].icon, true);

    #ifdef PBL_COLOR
    graphics_context_set_text_color(ctx, GColorYellow);
    #else
    graphics_context_set_text_color(ctx, GColorWhite);
    #endif
    int lbl_y = icon_y + 16;
    graphics_draw_text(ctx, "MEMORIZE YOUR CARDS!", f_sm,
      GRect(0, lbl_y, w, 16),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);

    int card_y = lbl_y + 20;
    int gw = cw * 2 + gap, gx = (w - gw) / 2;
    for(int i = 0; i < HAND_SIZE; i++) {
      int col = i % 2, row = i / 2;
      draw_card_gfx(ctx, gx + col*(cw+gap), card_y + row*(ch+gap),
        cw, ch, p->hand[i], true, row == 0);
    }

    graphics_context_set_text_color(ctx, GColorWhite);
    int below = card_y + 2*(ch+gap) + 4;
    graphics_draw_text(ctx, "Top 2 will be hidden!", f_sm,
      GRect(0, below, w, 16),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
    graphics_draw_text(ctx, "SELECT when memorized", f_sm,
      GRect(0, below+18, w, 16),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
  }

  // ======== PLAY ========
  else if(s_state == ST_PLAY) {
    int cp = cur_player();
    Player *p = &s_players[cp];

    int icon_y = PBL_IF_ROUND_ELSE(32, 18);
    draw_token(ctx, w/2, icon_y, s_players[cp].icon, true);

    int card_y = icon_y + 20;
    if(s_knocked) {
      #ifdef PBL_COLOR
      graphics_context_set_text_color(ctx, GColorRed);
      #else
      graphics_context_set_text_color(ctx, GColorWhite);
      #endif
      graphics_draw_text(ctx, "LAST TURN!", f_md,
        GRect(0, card_y, w, 22),
        GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
      card_y += 22;
    }

    // Centered grid: [C0][C1] buf [Pile] / [C2][C3] buf [Cascade]
    int buf_gap = 14;
    int total_w = cw * 3 + gap + buf_gap;
    int gx = (w - total_w) / 2;
    int col0 = gx, col1 = gx + cw + gap;
    int col2 = gx + cw*2 + gap + buf_gap;
    int row0 = card_y, row1 = card_y + ch + gap;

    // Player's 4 cards
    int hp[][2] = {{col0,row0},{col1,row0},{col0,row1},{col1,row1}};
    for(int i = 0; i < HAND_SIZE; i++)
      draw_card_gfx(ctx, hp[i][0], hp[i][1], cw, ch,
        p->hand[i], p->face_up[i], false);

    // Draw pile (cursor 0)
    draw_pile_gfx(ctx, col2, row0, cw, ch, deck_remaining(), s_cursor == 0);

    // Cascaded discard pile (cursor 1)
    int casc_n = 3;
    draw_discard_cascade(ctx, col2, row1, cw, ch, casc_n, s_cursor == 1);

    // Knock button under player cards (cursor 2, only if !knocked)
    if(!s_knocked) {
      int knock_y = row1 + ch + 6;
      int knock_w = cw * 2 + gap;
      int knock_x = col0;
      bool ksel = (s_cursor == 2);
      #ifdef PBL_COLOR
      graphics_context_set_fill_color(ctx, ksel ? GColorRed : GColorFromHEX(0x440000));
      #else
      graphics_context_set_fill_color(ctx, ksel ? GColorWhite : GColorDarkGray);
      #endif
      graphics_fill_rect(ctx, GRect(knock_x, knock_y, knock_w, 24), 6, GCornersAll);
      #ifdef PBL_COLOR
      graphics_context_set_stroke_color(ctx, ksel ? GColorWhite : GColorDarkGray);
      #else
      graphics_context_set_stroke_color(ctx, ksel ? GColorBlack : GColorLightGray);
      #endif
      graphics_context_set_stroke_width(ctx, 1);
      graphics_draw_round_rect(ctx, GRect(knock_x, knock_y, knock_w, 24), 6);
      #ifdef PBL_COLOR
      graphics_context_set_text_color(ctx, ksel ? GColorWhite : GColorLightGray);
      #else
      graphics_context_set_text_color(ctx, ksel ? GColorBlack : GColorWhite);
      #endif
      graphics_draw_text(ctx, "KNOCK", f_md,
        GRect(knock_x, knock_y + 1, knock_w, 22),
        GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
    }
  }

  // ======== DRAWN (visual card grid) ========
  else if(s_state == ST_DRAWN) {
    int cp = cur_player();
    Player *p = &s_players[cp];

    int icon_y = PBL_IF_ROUND_ELSE(32, 18);
    draw_token(ctx, w/2, icon_y, s_players[cp].icon, true);

    // 2x3 grid: [C0][C1] buf [Drawn] / [C2][C3] buf [Discard cascade]
    int buf_gap = 14;
    int total_w = cw * 3 + gap + buf_gap;
    int gx = (w - total_w) / 2;
    int col0 = gx, col1 = gx + cw + gap;
    int col2 = gx + cw*2 + gap + buf_gap;
    int card_y = icon_y + 20;
    int row0 = card_y, row1 = card_y + ch + gap;

    // Player's 4 cards
    int hp[][2] = {{col0,row0},{col1,row0},{col0,row1},{col1,row1}};
    for(int i = 0; i < HAND_SIZE; i++)
      draw_card_gfx(ctx, hp[i][0], hp[i][1], cw, ch,
        p->hand[i], p->face_up[i], s_cursor == i);

    // Drawn card (top-right, green border)
    draw_card_gfx(ctx, col2, row0, cw, ch, s_drawn_card, true, false);
    #ifdef PBL_COLOR
    graphics_context_set_stroke_color(ctx, GColorGreen);
    #else
    graphics_context_set_stroke_color(ctx, GColorWhite);
    #endif
    graphics_context_set_stroke_width(ctx, 2);
    graphics_draw_round_rect(ctx, GRect(col2, row0, cw, ch), 3);

    // Discard cascade (bottom-right, cursor HAND_SIZE)
    if(s_discard_count > 0) {
      draw_discard_cascade(ctx, col2, row1, cw, ch, 2, s_cursor == HAND_SIZE);
    } else {
      #ifdef PBL_COLOR
      graphics_context_set_stroke_color(ctx,
        s_cursor == HAND_SIZE ? GColorYellow : GColorDarkGray);
      #else
      graphics_context_set_stroke_color(ctx,
        s_cursor == HAND_SIZE ? GColorWhite : GColorDarkGray);
      #endif
      graphics_context_set_stroke_width(ctx, s_cursor == HAND_SIZE ? 2 : 1);
      graphics_draw_round_rect(ctx, GRect(col2, row1, cw, ch), 3);
    }
    // "X" marker on discard option
    graphics_context_set_text_color(ctx, GColorLightGray);
    int disc_top_y = row1;
    if(s_discard_count > 1) disc_top_y += 14;
    graphics_draw_text(ctx, "X", f_sm,
      GRect(col2 + cw - 10, disc_top_y, 10, 14),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);

    // Value hint
    #ifdef PBL_COLOR
    graphics_context_set_text_color(ctx, GColorYellow);
    #else
    graphics_context_set_text_color(ctx, GColorWhite);
    #endif
    char vh[16]; snprintf(vh, sizeof(vh), "%s = %d",
      card_str(s_drawn_card), card_value(s_drawn_card));
    int hy = row1 + ch + 4;
    if(s_discard_count > 1) hy += 14;
    graphics_draw_text(ctx, vh, f_sm,
      GRect(0, hy, w, 16),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
  }

  // ======== BLACKOUT (only for first-time players) ========
  else if(s_state == ST_BLACKOUT) {
    int cp = cur_player();
    graphics_context_set_fill_color(ctx, GColorBlack);
    graphics_fill_rect(ctx, b, 0, GCornerNone);

    int cy = h/2 - 40;
    graphics_context_set_text_color(ctx, GColorWhite);
    graphics_draw_text(ctx, "Pass watch to", f_sm,
      GRect(0, cy, w, 16),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
    draw_token(ctx, w/2, cy+36, s_players[cp].icon, true);
    #ifdef PBL_COLOR
    graphics_context_set_text_color(ctx, tok_color(s_players[cp].icon));
    #else
    graphics_context_set_text_color(ctx, GColorWhite);
    #endif
    graphics_draw_text(ctx, s_tok_name[s_players[cp].icon], f_lg,
      GRect(0, cy+50, w, 32),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
    graphics_context_set_text_color(ctx, GColorWhite);
    graphics_draw_text(ctx, "SELECT when ready", f_sm,
      GRect(0, h-PBL_IF_ROUND_ELSE(34, 24), w, 16),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
  }

  // ======== GAMEOVER ========
  else if(s_state == ST_GAMEOVER) {
    #ifdef PBL_COLOR
    graphics_context_set_text_color(ctx, GColorYellow);
    #else
    graphics_context_set_text_color(ctx, GColorWhite);
    #endif
    int ty = PBL_IF_ROUND_ELSE(pad+10, pad);
    graphics_draw_text(ctx, "GAME OVER!", f_lg,
      GRect(0, ty, w, 32),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);

    int scores[MAX_PLAYERS]; int lo = 999;
    for(int i=0; i<s_num_players; i++){
      scores[i] = hand_score(i);
      if(scores[i] < lo) lo = scores[i];
    }

    int ly = ty + 34;
    int rh = (s_num_players <= 4) ? 32 : 28;
    for(int i = 0; i < s_num_players; i++) {
      int pi = s_order[i];
      bool win = (scores[pi] == lo);
      int lx = PBL_IF_ROUND_ELSE(pad + 26, pad + 12);
      draw_token(ctx, lx, ly + rh/2, s_players[pi].icon, false);
      // Draw 4 mini cards
      int mcx = lx + 16;
      for(int j = 0; j < HAND_SIZE; j++) {
        draw_mini_card(ctx, mcx + j*22, ly+2, s_players[pi].hand[j], true);
      }
      // Score with WIN inline
      char sc[16];
      if(win)
        snprintf(sc, sizeof(sc), "=%d WIN", scores[pi]);
      else
        snprintf(sc, sizeof(sc), "=%d", scores[pi]);
      #ifdef PBL_COLOR
      graphics_context_set_text_color(ctx, win ? GColorYellow : GColorWhite);
      #else
      graphics_context_set_text_color(ctx, GColorWhite);
      #endif
      graphics_draw_text(ctx, sc, f_sm,
        GRect(mcx + 4*22 + 2, ly + 6, 50, 20),
        GTextOverflowModeTrailingEllipsis, GTextAlignmentLeft, NULL);
      ly += rh;
    }
    graphics_context_set_text_color(ctx, GColorWhite);
    graphics_draw_text(ctx, "SELECT: new game", f_sm,
      GRect(0, h-PBL_IF_ROUND_ELSE(26, 18), w, 16),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
  }

  // ======== OVERLAYS ========

  // Standings (hold UP) — mini cards
  if(s_show_standings && s_state >= ST_PLAY && s_state <= ST_DRAWN) {
    graphics_context_set_fill_color(ctx, GColorBlack);
    int op = pad + 8;
    graphics_fill_rect(ctx, GRect(op, op, w-op*2, h-op*2), 8, GCornersAll);
    int ly = op + 6;
    graphics_context_set_text_color(ctx, GColorWhite);
    graphics_draw_text(ctx, "STANDINGS", f_md,
      GRect(op, ly, w-op*2, 22),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
    ly += 26;

    for(int i = 0; i < s_num_players; i++) {
      int pi = s_order[i];
      bool cur = (i == s_cur_idx);
      Player *pl = &s_players[pi];
      int sx = PBL_IF_ROUND_ELSE((w - 116) / 2, op + 14);
      draw_token(ctx, sx, ly+14, pl->icon, false);
      // 4 mini cards (face_up OR temp_vis shows the card)
      for(int j = 0; j < HAND_SIZE; j++)
        draw_mini_card(ctx, sx + 16 + j*22, ly, pl->hand[j],
          pl->face_up[j] || pl->temp_vis[j]);
      // Highlight current player
      if(cur) {
        #ifdef PBL_COLOR
        graphics_context_set_stroke_color(ctx, GColorYellow);
        graphics_context_set_stroke_width(ctx, 1);
        graphics_draw_round_rect(ctx, GRect(op+2, ly-1, w-op*2-4, 28), 4);
        #endif
      }
      ly += 30;
    }
  }

  // History (hold DOWN) — mini cards
  if(s_show_history && s_state >= ST_PLAY && s_state <= ST_DRAWN) {
    graphics_context_set_fill_color(ctx, GColorBlack);
    int op = pad + 8;
    graphics_fill_rect(ctx, GRect(op, op, w-op*2, h-op*2), 8, GCornersAll);
    int ly = op + 6;
    #ifdef PBL_COLOR
    graphics_context_set_text_color(ctx, GColorYellow);
    #else
    graphics_context_set_text_color(ctx, GColorWhite);
    #endif
    graphics_draw_text(ctx, "SINCE YOUR TURN", f_md,
      GRect(op, ly, w-op*2, 22),
      GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
    ly += 26;

    int start = s_log_turn_start[cur_player()];
    int shown = 0;
    for(int i = start; i < s_log_count && shown < 6; i++) {
      LogEntry *e = &s_log[i];
      if(e->player >= 0)
        draw_token(ctx, op+12, ly+14, s_players[e->player].icon, false);
      draw_mini_card(ctx, op+28, ly, e->card, true);
      ly += 30;
      shown++;
    }
    if(shown == 0) {
      graphics_context_set_text_color(ctx, GColorLightGray);
      graphics_draw_text(ctx, "Nothing yet!", f_sm,
        GRect(op, ly, w-op*2, 18),
        GTextOverflowModeTrailingEllipsis, GTextAlignmentCenter, NULL);
    }
  }
}

// ============================================================================
// TRANSITION
// ============================================================================
static void goto_next(void) {
  int cp = cur_player();
  s_log_turn_start[cp] = s_log_count;
  next_player();
  if(s_knocked && s_cur_idx == s_knocker_idx) {
    s_state = ST_GAMEOVER;
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
    int np = cur_player();
    if(!s_players[np].seen_cards) {
      // First turn: go straight to instructions (no blackout)
      s_state = ST_INSTRUCT;
    } else {
      // Skip blackout, go straight to play
      // Clear expired temp visibility
      if(s_has_temp_vis && s_cur_idx == s_temp_vis_clear_at) {
        for(int i = 0; i < s_num_players; i++)
          for(int j = 0; j < HAND_SIZE; j++)
            s_players[i].temp_vis[j] = false;
        s_has_temp_vis = false;
      }
      s_cursor = 0;
      s_log_turn_start[np] = s_log_count;
      s_state = ST_PLAY;
    }
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
    deal_hands();
    s_cur_idx = 0; s_rounds = 1; s_knocked = false;
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
      s_drew_from_discard = false;
      s_cursor = 0;
      s_state = ST_DRAWN;
    } else if(s_cursor == 1) {
      // Take from discard
      s_drawn_card = pop_discard();
      s_drew_from_discard = true;
      s_cursor = 0;
      s_state = ST_DRAWN;
    } else if(s_cursor == 2 && !s_knocked) {
      s_knocked = true;
      s_knocker_idx = s_cur_idx;
      vibes_short_pulse();
      goto_next();
    }
  }
  else if(s_state == ST_DRAWN) {
    int cp = cur_player();
    if(s_cursor < HAND_SIZE) {
      // Replace card — face_up stays unchanged (face-down stays hidden)
      Card old = s_players[cp].hand[s_cursor];
      s_players[cp].hand[s_cursor] = s_drawn_card;
      // If slot was face-down and taken from discard, temp-visible for 1 turn
      if(!s_players[cp].face_up[s_cursor] && s_drew_from_discard) {
        s_players[cp].temp_vis[s_cursor] = true;
        s_has_temp_vis = true;
        s_temp_vis_clear_at = (s_cur_idx + 2) % s_num_players;
      }
      push_discard(old);
      log_discard(old, cp);
    } else {
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
  if(s_state == ST_SETUP || s_state == ST_GAMEOVER)
    window_stack_pop(true);
  else {
    s_state = ST_SETUP; s_setup_cursor = 0;
    if(s_canvas) layer_mark_dirty(s_canvas);
  }
}

static void up_long_down(ClickRecognizerRef ref, void *ctx) {
  s_show_standings = true; if(s_canvas) layer_mark_dirty(s_canvas);
}
static void up_long_up(ClickRecognizerRef ref, void *ctx) {
  s_show_standings = false; if(s_canvas) layer_mark_dirty(s_canvas);
}
static void down_long_down(ClickRecognizerRef ref, void *ctx) {
  s_show_history = true; if(s_canvas) layer_mark_dirty(s_canvas);
}
static void down_long_up(ClickRecognizerRef ref, void *ctx) {
  s_show_history = false; if(s_canvas) layer_mark_dirty(s_canvas);
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
// WINDOW & LIFECYCLE
// ============================================================================
static void win_load(Window *w) {
  Layer *wl = window_get_root_layer(w);
  GRect b = layer_get_bounds(wl);
  s_canvas = layer_create(b);
  layer_set_update_proc(s_canvas, canvas_proc);
  layer_add_child(wl, s_canvas);
  window_set_click_config_provider(w, click_config);
  s_state = ST_SETUP; s_setup_cursor = 0;
}

static void win_unload(Window *w) {
  if(s_canvas) { layer_destroy(s_canvas); s_canvas = NULL; }
}

static void init(void) {
  srand(time(NULL));
  if(persist_exists(P_LO_SCORE)) s_lo_score = persist_read_int(P_LO_SCORE);
  s_icon_font_20 = fonts_load_custom_font(resource_get_handle(RESOURCE_ID_ICON_FONT_20));
  s_icon_font_14 = fonts_load_custom_font(resource_get_handle(RESOURCE_ID_ICON_FONT_14));
  s_win = window_create();
  window_set_background_color(s_win, GColorBlack);
  window_set_window_handlers(s_win, (WindowHandlers){.load=win_load,.unload=win_unload});
  window_stack_push(s_win, true);
}

static void deinit(void) {
  window_destroy(s_win);
  fonts_unload_custom_font(s_icon_font_20);
  fonts_unload_custom_font(s_icon_font_14);
}

int main(void) { init(); app_event_loop(); deinit(); return 0; }
