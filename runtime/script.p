#set terminal postscript eps enhanced color
#set out 'pbft.eps'

set term png
set output 'pbft.png'

#set multiplot layout 1,1 rowsfirst

set autoscale
unset log
unset label
set xtic auto
set ytic auto
unset key

set style line 1 lt 1 lw 1 pt 1 linecolor rgb "blue"

set title "#replicas=R, #clients=C, #requests=X"
set xlabel "timestamp/instance"
set ylabel "average time in ms"
set yr [9:10.0]	 

plot "pbft.dat" using 1:2 with line ls 1
