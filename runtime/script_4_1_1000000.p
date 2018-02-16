#set terminal postscript eps enhanced color size 800,500
#set output 'pbft_4_1_1000000.eps'

set term png size 800,500
set output 'pbft_4_1_1000000.png'

#set multiplot layout 1,1 rowsfirst

set autoscale
unset log
unset label
set xtic auto
set ytic auto
unset key

set style line 1 lt 1 lw 1 pt 1 linecolor rgb "red"
#set style line 2 lt 1 lw 1 pt 1 linecolor rgb "blue"
#$set style line 3 lt 1 lw 1 pt 1 linecolor rgb "green"

set xlabel "timestamp/instance"
set ylabel "average response time in ms"
set yr [6.0:10.0]	 
set format x "%g"
#set format x "%.0s*10^%T"

plot "pbft_avg_0_4_1_1000000.dat"  using 1:2 with line ls 1
#   , \
#     "pbft_avg_0_7_1_1000000.dat"  using 1:2 with line ls 2, \
#     "pbft_avg_0_10_1_1000000.dat" using 1:2 with line ls 3
