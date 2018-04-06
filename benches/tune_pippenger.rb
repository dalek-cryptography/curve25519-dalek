#!/usr/bin/env ruby

def straus_cost(n, w=5, add=1.0, readd=0.9, double=0.7)
	windows = (256+w-1)/w;
	premult = (2**(w-2) - 1)*add + 1*double;
	n*(                # for each point...
		premult +      # ... premultiply once,
		windows*readd  # and re-add premultiplied point for each window
	) + 255*double     # bitshift the accumulator for each bit
end

def pippenger_cost(n, w, add=1.0, readd=0.9, double=0.7)
	windows = (256+w-1)/w;
	windows.to_f*(
		n*readd +                    # adding each point to some bucket
		2*(2**(w-1) - 1 - 1)*add +   # adding buckets, without zero-th, without first one ('cos n-1 additions for n items).
		add +                        # adding to result (can actually skip the first one, but it does not matter too much)
		w*double                     # shifting words by w bits each
	) - w*double                     # we are not shifting the first one
end

def straus_mem(w)
	(2**(w-2))*(4*5*64/8)
end

def pippenger_mem(w)
	[(2**(w-1) - 1 - 1)*(4*5*64/8), 0].max
end

def main

	straus_ws = 5..5
	pippenger_ws = 1..22


	n_f = 1;
	last_n = 0;
	print "      n     "
	straus_ws.each do |w|
		print "Stra.w=%02d     " % [w]
	end	
	pippenger_ws.each do |w|
		print "Pipp.w=%02d     " % [w]
	end
	print "\n"
	puts "-"*271
	print "Memory:  "
	straus_ws.each do |w|
		print "% 12d  " % [straus_mem(w)]
	end
	pippenger_ws.each do |w|
		print "% 12d  " % [pippenger_mem(w)]
	end
	print "\n"
	puts "-"*271
	while n_f < 130+(15*1_000_000)
		n = n_f.round
		if n > last_n # filter duplicates
			last_n = n

			scs = straus_ws.map {|w| straus_cost(n, w) }
			pcs = pippenger_ws.map {|w| pippenger_cost(n,w) }

			minimum = (scs+pcs).min
			sc_min = (scs).min
			pp_min = (pcs).min

			print "% 9d" % [n]
			scs.each do |sc|
				print(("% 12d  " % [sc]).colorize_if(sc == minimum || sc == sc_min, sc_min == minimum ? 32 : 33))
			end
			pcs.each do |pc|
				print(("% 12d  " % [pc]).colorize_if(pc == minimum || pc == pp_min, pp_min == minimum ? 32 : 33))
			end

			print "\n"
		end
		n_f *= (2**(1.0/8.0))
	end
end

class String
  # colorization
  def colorize(color_code)
    "\e[#{color_code}m#{self}\e[0m"
  end

  def colorize_if(boolean, color_code)
  	if boolean
    	"\e[#{color_code}m#{self}\e[0m"
    else
    	self
    end
  end

  def red
    colorize(31)
  end

  def green
    colorize(32)
  end

  def yellow
    colorize(33)
  end

  def blue
    colorize(34)
  end

  def pink
    colorize(35)
  end

  def light_blue
    colorize(36)
  end
end

main
