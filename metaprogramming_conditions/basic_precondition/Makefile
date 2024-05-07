# distributed algorithms, n.dulay, 3 jan 23 
# Makefile, v1

START    = BasicDeadlock.start
MAX_TIME = 10000

HOST	:= 127.0.0.1
ELIXIR  := elixir --no-halt --cookie ${COOKIE} --name
MIX 	:= -S mix run -e ${START}

compile:
	mix compile

clean:
	mix clean
	@rm -f erl_crash.dump

# make ps - lists Elixir nodes running locally
ps:
	@echo ------------------------------------------------------------
	epmd -names

# --------------------------------------------------------------------

# make single 
#	runs 1 client and 1 server process on the elixir node 
#    	'clientserver_LOGIN@127.0.0.1'

single: compile
	mix run -e "BasicDeadlock.start(:run)"
# --------------------------------------------------------------------

# make cluster
#	runs 1 client process on the elixir node 'client_SUFFIX@127.0.0.1'
#    	     1 server process on the elixir node 'server_SUFFIX@127.0.0.1'
# 	sleeps 1 second to allow the forked client and server nodes
#	to start in the background before starting clientserver in 
#    	the foreground

# run cluster: compile
# 	@ ${ELIXIR} client1_${NODE_SUFFIX} ${MIX} cluster_wait &
# 	@ ${ELIXIR} client2_${NODE_SUFFIX} ${MIX} cluster_wait &
# 	@ ${ELIXIR} client3_${NODE_SUFFIX} ${MIX} cluster_wait &
# 	@ ${ELIXIR} client4_${NODE_SUFFIX} ${MIX} cluster_wait &
# 	@ ${ELIXIR} client5_${NODE_SUFFIX} ${MIX} cluster_wait &
# 	@ ${ELIXIR} server_${NODE_SUFFIX} ${MIX} cluster_wait & 
# 	@sleep 1
# 	@ ${ELIXIR} clientserver_${NODE_SUFFIX} ${MIX} cluster_start

# --------------------------------------------------------------------

# Notes 
#   -- 	elixir nodes run as Linux processes
#   -- 	all nodes run on localhost (127.0.0.1) and will exit after
#   	max_time milliseconds
#   -- 	the cookie string is use to 'verify' nodes to each other in 
#   	the cluster
