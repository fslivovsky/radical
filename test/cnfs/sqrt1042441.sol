c ---- [ banner ] ------------------------------------------------------------
c 
c CaDiCaL Radically Simplified CDCL SAT Solver
c Version 02d b708271496f7d759e017985a84b04761b572c0e6
c Copyright (c) 2016 Armin Biere, JKU
c 
c Wed Nov  9 13:01:54 CET 2016
c g++ (Ubuntu 5.4.0-6ubuntu1~16.04.2) 5.4.0 20160609
c Linux fmvi7ab 4.4.0-38-generic x86_64
c g++ -Wall -O3
c 
c ---- [ parsing input ] -----------------------------------------------------
c 
c reading DIMACS file from 'cnfs/sqrt1042441.cnf'
c opening file to read 'cnfs/sqrt1042441.cnf'
c found 'p cnf 659 1877' header
c initialized 659 variables
c parsed 1877 clauses in 0.00 seconds
c closing file 'cnfs/sqrt1042441.cnf'
c after reading 22747 bytes 0.0 MB
c 
c ---- [ options ] -----------------------------------------------------------
c 
c --arena=3
c --binary=true
c --check=true
c --clim=-1
c --dlim=-1
c --elim=true
c --elimclslim=1000
c --elimignore=0
c --eliminit=1000
c --elimint=10000
c --elimocclim=100
c --elimroundsinit=5
c --elimrounds=2
c --emabumplast=1e-05
c --emagluefast=0.03
c --emaglueslow=1e-05
c --emajump=1e-05
c --emarestarteff=0.001
c --emarestartint=1e-05
c --emasize=1e-05
c --keepglue=2
c --keepsize=3
c --leak=true
c --minimize=true
c --minimizedepth=1000
c --prefetch=true
c --profile=2
c --quiet=false
c --reduce=true
c --reduceglue=true
c --reduceinc=300
c --reduceinit=2000
c --restart=true
c --restartint=4
c --restartmargin=1.1
c --reusetrail=true
c --shrink=true
c --shrinkdepth=2
c --shrinkglue=5
c --shrinksize=20
c --strengthen=true
c --sublast=5
c --subsume=true
c --subsumeinc=10000
c --subsumeinit=10000
c --subsumeocclim=100
c --trailbump=true
c --trailbumplast=40
c --trailbumprops=200
c --verbose=false
c --witness=true
c 
c ---- [ proof tracing ] -----------------------------------------------------
c 
c opening file to write 'cnfs/sqrt1042441.proof'
c writing binary DRAT proof trace to 'cnfs/sqrt1042441.proof'
c 
c ---- [ solving ] -----------------------------------------------------------
c 
c
c  seconds    reductions      redundant    irredundant     restarteff      propdec
c         MB       restarts           glue       variables      restartint     propconf
c           level       conflicts         size        remaining       bumplast
c
c i  0.00  0  0.0  0    0     1     0 1.0  1.0 1876 339 51.4% 0.00  0.0 8.3% 486 486
c 1  0.00  0  0.0  0    0     1     0 1.0  1.0 1876 339 51.4% 0.00  0.0 8.3% 412 825
c 
c ---- [ closing proof ] -----------------------------------------------------
c 
c closing file 'cnfs/sqrt1042441.proof'
c after writing 1245 bytes 0.0 MB
c 
c ---- [ result ] ------------------------------------------------------------
c 
s SATISFIABLE
v 1 2 -3 4 5 6 7 8 9 10 11 -12 -13 -14 15 -16 -17 18 19 -20 -21 22 -23 24 -25
v -26 27 -28 -29 30 -31 -32 33 34 -35 -36 -37 -38 39 40 -41 -42 43 -44 -45 46
v -47 -48 49 50 -51 -52 -53 -54 55 -56 -57 58 -59 -60 61 62 -63 -64 65 -66 67
v 68 -69 70 -71 -72 73 -74 -75 76 77 -78 -79 -80 -81 82 83 -84 -85 -86 87 -88
v -89 90 -91 -92 -93 94 95 -96 -97 98 -99 100 101 -102 -103 104 -105 -106 107
v -108 -109 110 111 -112 -113 -114 -115 116 117 -118 -119 -120 -121 122 123
v -124 -125 -126 127 -128 -129 130 -131 -132 -133 134 135 -136 -137 138 -139
v 140 141 -142 143 -144 -145 146 -147 -148 149 -150 -151 152 153 -154 -155
v -156 -157 158 159 -160 -161 -162 -163 164 165 -166 -167 -168 -169 170 171
v -172 -173 -174 175 -176 -177 178 -179 -180 -181 182 183 -184 -185 186 -187
v 188 189 -190 191 -192 -193 -194 195 -196 -197 198 -199 -200 201 202 -203
v -204 -205 -206 207 208 -209 -210 -211 -212 213 214 -215 -216 -217 -218 219
v 220 -221 -222 -223 -224 225 226 -227 -228 -229 230 -231 -232 233 -234 -235
v -236 237 238 -239 -240 241 -242 243 244 -245 246 -247 248 -249 -250 -251 252
v -253 -254 255 -256 -257 258 259 -260 -261 -262 -263 264 265 -266 -267 -268
v -269 270 271 -272 -273 -274 -275 276 277 -278 -279 -280 -281 282 283 -284
v -285 -286 -287 288 289 -290 -291 -292 293 -294 -295 296 -297 -298 -299 300
v 301 -302 -303 -304 305 306 -307 308 -309 310 -311 -312 -313 -314 315 -316
v 317 -318 -319 -320 321 322 -323 -324 -325 -326 327 328 -329 -330 -331 -332
v 333 334 -335 -336 -337 -338 339 340 -341 -342 -343 -344 345 346 -347 -348
v -349 -350 351 352 -353 -354 -355 -356 357 -358 -359 360 -361 -362 363 364
v -365 -366 -367 368 369 370 -371 372 -373 374 -375 -376 -377 -378 -379 -380
v 381 382 -383 -384 -385 -386 387 388 -389 -390 -391 -392 393 394 -395 -396
v -397 -398 399 400 -401 -402 -403 -404 405 406 -407 -408 -409 -410 411 412
v -413 -414 -415 -416 417 -418 -419 420 421 -422 -423 -424 -425 426 -427 428
v 429 430 -431 432 -433 -434 -435 -436 -437 438 -439 -440 -441 -442 443 444
v -445 -446 -447 -448 449 450 -451 -452 -453 -454 455 456 -457 -458 -459 -460
v 461 462 -463 -464 -465 -466 467 468 -469 -470 -471 472 -473 -474 -475 476
v 477 -478 -479 -480 481 -482 483 -484 485 -486 -487 -488 -489 490 -491 -492
v -493 -494 495 496 -497 -498 -499 -500 501 502 -503 -504 -505 -506 507 508
v -509 -510 -511 -512 513 514 -515 -516 -517 -518 519 520 -521 -522 -523 -524
v 525 -526 527 -528 529 -530 -531 -532 -533 534 -535 -536 -537 -538 539 540
v -541 -542 -543 -544 545 546 -547 -548 -549 -550 551 552 -553 -554 -555 -556
v 557 558 -559 -560 -561 -562 563 -564 565 -566 567 -568 -569 -570 571 -572
v -573 -574 -575 576 577 -578 -579 -580 -581 582 583 -584 -585 -586 -587 588
v 589 -590 -591 -592 -593 594 -595 596 -597 -598 -599 600 -601 -602 -603 -604
v 605 606 -607 -608 -609 -610 611 612 -613 -614 -615 -616 617 -618 619 -620
v -621 622 -623 -624 -625 -626 627 628 -629 -630 -631 -632 633 -634 635 -636
v -637 -638 -639 -640 641 642 643 644 645 646 647 648 649 650 651 652 653 654
v 655 656 657 658 659
v 0
c 
c ---- [ run-time profiling data ] -------------------------------------------
c 
c         0.00    0.00% collect
c         0.00    0.00% elim
c         0.00    0.00% parse
c         0.00    0.00% reduce
c         0.00    0.00% search
c         0.00    0.00% simplify
c         0.00    0.00% subsume
c   ===============================
c         0.00  100.00% all
c 
c ---- [ statistics ] --------------------------------------------------------
c 
c eliminations:                0         0.00    conflicts per elimination
c subsumptions:                0         0.00    conflicts per subsumption
c reductions:                  0         0.00    conflicts per reduction
c restarts:                    0         0.00    conflicts per restart
c conflicts:                   1         0.00    per second
c decisions:                   2         0.00    per second
c propagations:              825         0.00    millions per second
c reused:                      0         0.00 %  per restart
c resolved:                    0         0.00    per eliminated
c eliminated:                  0         0.00 %  of all variables
c fixed:                     320        48.56 %  of all variables
c units:                       1         1.00    conflicts per unit
c binaries:                    0         0.00    conflicts per binary
c trailbumped:                 0         0.00 %  per conflict
c analyzed:                    0         0.00    per conflict
c learned:                     1         1.00    per conflict
c minimized:                   0         0.00 %  of 1st-UIP-literals
c forward:                     0         0.00    tried per forward
c strengthened:                0         0.00    per forward
c shrunken:                    0         0.00 %  of tried literals
c backward:                    0         0.00 %  per conflict
c searched:                    4         2.00    per decision
c bumped:                    719       719.00    per conflict
c reduced:                     0         0.00 %  clauses per conflict
c collections:                 0         0.00    conflicts per collection
c collected:                   0         0.00    bytes and MB
c maxbytes:               253020         0.24    bytes and MB
c time:                                  0.00    seconds
c 
c exit 10
