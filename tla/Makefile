all: SynchronousL2

SynchronousL2: SynchronousL2.tla SynchronousL2.cfg
	pcal SynchronousL2.tla
	tlc -modelcheck $<
	# tlc -dfid 16 $<
	# tlc -simulate $<
