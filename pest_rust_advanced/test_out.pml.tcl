# maxx 1
# maxx 2
# maxx 3
# maxx 4
# maxx 5
# maxx 6
# maxx 7
# Scaler 0.401786, MH 1493
wm title . "scenario"
wm geometry . 1440x600+650+100
canvas .c -width 800 -height 800 \
	-scrollregion {0c -1c 30c 100c} \
	-xscrollcommand ".hscroll set" \
	-yscrollcommand ".vscroll set" \
	-bg white -relief raised -bd 2
scrollbar .vscroll -relief sunken  -command ".c yview"
scrollbar .hscroll -relief sunken -orient horiz  -command ".c xview"
pack append . \
	.vscroll {right filly} \
	.hscroll {bottom fillx} \
	.c {top expand fill}
.c yview moveto 0
# ProcLine[1] stays at 0 (Used 0 nobox 0)
.c create rectangle 104 0 180 20 -fill black
# ProcLine[1] stays at 0 (Used 0 nobox 0)
.c create rectangle 103 -2 177 18 -fill ivory
.c create text 140 8 -text "0::init:"
.c create text 70 32 -fill #eef -text "1"
.c create line 140 32 1260 32 -fill #eef -dash {6 4}
.c create line 300 36 300 20 -fill lightgrey -tags grid -width 1 
.c lower grid
# ProcLine[2] from 0 to 1 (Used 0 nobox 0)
.c create rectangle 246 24 358 44 -fill black
# ProcLine[2] stays at 1 (Used 0 nobox 0)
.c create rectangle 244 22 356 42 -fill ivory
.c create text 300 32 -text "1:start_link"
.c create text 70 56 -fill #eef -text "3"
.c create line 140 56 1260 56 -fill #eef -dash {6 4}
.c create line 460 36 460 44 -fill lightgrey -tags grid -width 1 
.c lower grid
# ProcLine[3] from 0 to 3 (Used 0 nobox 0)
.c create rectangle 400 48 524 68 -fill black
# ProcLine[3] stays at 3 (Used 0 nobox 0)
.c create rectangle 399 46 521 66 -fill ivory
.c create text 460 56 -text "2:accept_loop"
.c create text 70 80 -fill #eef -text "5"
.c create line 140 80 1260 80 -fill #eef -dash {6 4}
.c create line 620 36 620 68 -fill lightgrey -tags grid -width 1 
.c lower grid
# ProcLine[4] from 0 to 5 (Used 0 nobox 0)
.c create rectangle 566 72 678 92 -fill black
# ProcLine[4] stays at 5 (Used 0 nobox 0)
.c create rectangle 564 70 676 90 -fill ivory
.c create text 620 80 -text "3:start_link"
.c create text 70 104 -fill #eef -text "7"
.c create line 140 104 1260 104 -fill #eef -dash {6 4}
.c create line 780 36 780 92 -fill lightgrey -tags grid -width 1 
.c lower grid
# ProcLine[5] from 0 to 7 (Used 0 nobox 0)
.c create rectangle 720 96 844 116 -fill black
# ProcLine[5] stays at 7 (Used 0 nobox 0)
.c create rectangle 719 94 841 114 -fill ivory
.c create text 780 104 -text "4:accept_loop"
.c create text 70 128 -fill #eef -text "9"
.c create line 140 128 1260 128 -fill #eef -dash {6 4}
.c create line 940 36 940 116 -fill lightgrey -tags grid -width 1 
.c lower grid
# ProcLine[6] from 0 to 9 (Used 0 nobox 0)
.c create rectangle 886 120 998 140 -fill black
# ProcLine[6] stays at 9 (Used 0 nobox 0)
.c create rectangle 884 118 996 138 -fill ivory
.c create text 940 128 -text "5:start_link"
.c create text 70 152 -fill #eef -text "11"
.c create line 140 152 1260 152 -fill #eef -dash {6 4}
.c create line 1100 36 1100 140 -fill lightgrey -tags grid -width 1 
.c lower grid
# ProcLine[7] from 0 to 11 (Used 0 nobox 0)
.c create rectangle 1040 144 1164 164 -fill black
# ProcLine[7] stays at 11 (Used 0 nobox 0)
.c create rectangle 1039 142 1161 162 -fill ivory
.c create text 1100 152 -text "6:accept_loop"
.c create text 70 176 -fill #eef -text "13"
.c create line 140 176 1260 176 -fill #eef -dash {6 4}
.c create line 1260 36 1260 164 -fill lightgrey -tags grid -width 1 
.c lower grid
# ProcLine[8] from 0 to 13 (Used 0 nobox 0)
.c create rectangle 1187 168 1337 188 -fill black
# ProcLine[8] stays at 13 (Used 0 nobox 0)
.c create rectangle 1186 166 1334 186 -fill ivory
.c create text 1260 176 -text "7:start_proposer"
.c lower grid
.c raise mesg
