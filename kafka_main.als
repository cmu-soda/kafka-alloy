open actions
open invariants

/**
 * Initial state of the cluster
 *
 * @repFactor: configure the replication factor of the cluster
 */
pred Init[repFactor: Int] {
	Kafka.replicationFactor = repFactor
	InvariantsStrict[Kafka]
}

/**
 * Broker won't recover if InvariantsStrict satisfies in initial state
 * Instead InvariantsAfterCrash should satisfy before brokerRecover
 *
 * @repFactor: configure the replication factor of the cluster
 */
pred InitBeforeRecover[repFactor: Int] {
	Kafka.replicationFactor = repFactor
	InvariantsAfterCrash[Kafka]
}

/**
 * Predicate defining behaviour which allows traces where brokers crash until the cluster goes down
 */
pred kafkaSimpleBehavior[repFactor : Int] {
	-- Initial state --
	---------------
	Init[repFactor]

	-- Transition --
	--------------
	always (
		-- Execute some action or stay idle
		doSomething or doNothing
	)
}

/**
 * Predicate defining behaviour which adds a constraint which doesn't allow a broker to crash twice
 * without recovering first.
 */
pred kafkaFaultTolerantBehavior[repFactor : Int] {
	-- Initial state --
	---------------
	Init[repFactor]

	-- Transition --
	--------------
	always (
		-- Execute some action or stay idle
		(doSomething or doNothing)

		-- Can't allow brokers to keep crashing without a recovery in between
		and (executeBrokerCrash implies after((not executeBrokerCrash) until executeBrokerRecover))
	)
}

/**************************************************************************
 * VISUALISE SINGLE STEP ACTIONS WITH FOLLOWING RUN COMMANDS
 **************************************************************************/

run visualizeReadEvent {
	Init[2] and some Kafka.zookeeper.topics.partitions.leader.events
	executeReadEvent and after(doNothing)
} for 4

run visualizePushEvent {
	Init[2] and some Kafka.zookeeper.topics.partitions.leader.events
	executePushEvent and after(doNothing)
} for 4

run visualizeBrokerCrash {
	Init[3] and some Kafka.zookeeper.topics.partitions.leader.events
	executeBrokerCrash and after(doNothing)
} for 6

run visualizeBrokerRecover {
	InitBeforeRecover[3] and some Kafka.zookeeper.topics.partitions.leader.events
	executeBrokerRecover and after(doNothing)
} for 4
/**************************************************************************/



/****************************************** ASSERTIONS *****************************************/

/**
 * The invariant topicPartitionMustSatisfyReplicationFactor[] will
 * fail if a broker crashes because some replicas will be lost.
 * topicPartitionMustSatisfyReplicationFactor therefore does not hold
 *
 * RESULT:
 * Executing "Check InvariantsStrictAlwaysSatisfiesWithSimpleKafka for 4"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=4 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..2 steps. 71790 vars. 1606 primary vars. 202293 clauses. 1359ms.
 * Counterexample found. Assertion is invalid. 90ms.
 */
assert InvariantsStrictAlwaysSatisfiesWithSimpleKafka {
	-- Counterexample is expected for this assertion
	kafkaSimpleBehavior[3] implies always(InvariantsStrict[Kafka])
}
check InvariantsStrictAlwaysSatisfiesWithSimpleKafka for 4


/**
 * Asserts that Strict invariants satisfy for kafkaFaultTolerantBehavior
 * Assertion is expected to be invalid because broker is allowed to crash
 *
 * RESULT:
 * Executing "Check InvariantsStrictAlwaysSatisfiesWithFaultTolerantKafka for 4"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=4 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..3 steps. 136292 vars. 2988 primary vars. 404737 clauses. 10474ms.
 * Counterexample found. Assertion is invalid. 858ms.
 */
assert InvariantsStrictAlwaysSatisfiesWithFaultTolerantKafka {
	-- Counterexample is expected for this assertion
	kafkaFaultTolerantBehavior[3] implies always(InvariantsStrict[Kafka])
}
check InvariantsStrictAlwaysSatisfiesWithFaultTolerantKafka for 4


/**
 * The invariant InvariantsAfterCrash contains all invariants in
 * Invariants[Kafka] except topicPartitionMustSatisfyReplicationFactor[k]
 * which relaxes the condition on the exact number of replications of partitions.
 * However, it does expect some backup replica for each parition with
 * topicPartitionMustHaveBackups[k]. Assertion SimpleKafkaEventuallyViolatesInvariant
 * is expected to result in counterexamples because kafkaSimpleBehavior allows brokers
 * to keep crashing, eventually resulting in violation of topicPartitionMustHaveBackups[k]
 * 
 * The following assertion is expected to give a counterexample.
 * RESULT:
 * Executing "Check SimpleKafkaPreservesInvariantsAfterCrash for 3"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=3 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..3 steps. 68191 vars. 1626 primary vars. 190839 clauses. 1172ms.
 * Counterexample found. Assertion is invalid. 130ms.
 */
assert SimpleKafkaPreservesInvariantsAfterCrash {
	kafkaSimpleBehavior[3] implies always(InvariantsAfterCrash[Kafka])
}
check SimpleKafkaPreservesInvariantsAfterCrash for 3


/**
 * kafkaFaultTolerantBehavior[3] ensures that a broker recovers after it crashes
 * Therefore, assertion holds because at least 2 replicas are always maintained
 *
 * RESULT:
 * Executing "Check FaultTolerantKafkaWithThreeReplicasPreservesInvariantsAfterCrash for 3"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=3 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..10 steps. 554506 vars. 12895 primary vars. 1673253 clauses. 47385ms.
 * No counterexample found. Assertion may be valid. 30521ms.
 */
assert FaultTolerantKafkaWithThreeReplicasPreservesInvariantsAfterCrash {
	kafkaFaultTolerantBehavior[3] implies always(InvariantsAfterCrash[Kafka])
}
check FaultTolerantKafkaWithThreeReplicasPreservesInvariantsAfterCrash for 4


/**
 * The following assertion does not hold because replication of 2 would
 * leave no backup in case a broker goes down
 *
 * This assertion is expected to give a counterexample
 * RESULT:
 * Executing "Check FaultTolerantKafkaWithTwoReplicasPreservesInvariantsAfterCrash for 4"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=4 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..3 steps. 135962 vars. 2988 primary vars. 403807 clauses. 27795ms.
 * Counterexample found. Assertion is invalid. 800ms.
 */
assert FaultTolerantKafkaWithTwoReplicasPreservesInvariantsAfterCrash {
	kafkaFaultTolerantBehavior[2] implies always(InvariantsAfterCrash[Kafka])
}
check FaultTolerantKafkaWithTwoReplicasPreservesInvariantsAfterCrash for 4


/**
 * Asserts that InvariantsOtherThanReplication always satisfies for all behaviors of
 * Kafka
 *
 * RESULT:
 * Executing "Check InvariantsOtherThanReplicationAlwaysSatisfies for 3"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=3 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..10 steps. 551660 vars. 12895 primary vars. 1590556 clauses. 3384131ms.
 * Solving...
 * Solving Stopped. Stopped solving because it got too slow.
 * Assertion should be valid since No counterexample was found within 10 steps.
 */
assert InvariantsOtherThanReplicationAlwaysSatisfies {
	-- Counterexample is expected for this assertion
	all rep : Int | kafkaSimpleBehavior[rep] implies always(InvariantsOtherThanReplication[Kafka])
}
check InvariantsOtherThanReplicationAlwaysSatisfies for 3


/**
 * kafkaFaultTolerantBehavior ensures that a broker recovers after it crashes, leading
 * to satisfaction of replication factor criteria.
 * Therefore this assertion holds.
 *
 * RESULT:
 * Executing "Check BrokerRecoverPreservesStrictInvariantsUntilBrokerGoesDown for 3"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=3 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..10 steps. 617925 vars. 12895 primary vars. 1879123 clauses. 13169ms.
 * No counterexample found. Assertion may be valid. 193ms.
 */
assert BrokerRecoverPreservesStrictInvariantsUntilBrokerGoesDown {
	kafkaFaultTolerantBehavior[3] implies always (
		-- Strict invariants start to satisfy once a broker recovers
		(executeBrokerRecover implies after(InvariantsStrict[Kafka]))

		-- If a broker goes down, InvariantsAfterCrash satisfies until broker recovers
		and (executeBrokerCrash implies after(InvariantsAfterCrash[Kafka] until executeBrokerRecover))

		
	)
}
check BrokerRecoverPreservesStrictInvariantsUntilBrokerGoesDown for 3



/**
 * If broker never goes down, Strict invariants satisfy for either of the two behaviors:
 * kafkaSimpleBehavior or kafkaFaultTolerantBehavior
 *
 * RESULT:
 * Executing "Check NeverBrokerCrashPreservesStrictInvariants for 2 but exactly 4 PartitionReplica"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=2 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..10 steps. 271909 vars. 6870 primary vars. 807126 clauses. 24951ms.
 * No counterexample found. Assertion may be valid. 5982ms.
 */
assert NeverBrokerCrashPreservesStrictInvariants {
	(kafkaSimpleBehavior[2] or kafkaFaultTolerantBehavior[2]) implies
		((not eventually(executeBrokerCrash)) implies always(InvariantsStrict[Kafka]))
}
check NeverBrokerCrashPreservesStrictInvariants for 2


/**
 * LIVENESS: Everytime a broker crashes, it must recover at some point in the future
 * and must not crash again before that recovery
 *
 * RESULT: 
 * Executing "Check FaultTolerantKafkaEventuallyRecoversAfterCrash for 4"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=4 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..10 steps. 1152925 vars. 23520 primary vars. 3598479 clauses. 37418ms.
 * No counterexample found. Assertion may be valid. 383ms.
 */
assert FaultTolerantKafkaEventuallyRecoversAfterCrash {
	kafkaFaultTolerantBehavior[3] implies always (executeBrokerCrash implies (
		-- Eventually recover
		eventually(executeBrokerRecover)

		-- No crash before recovery
		and after((not executeBrokerCrash) until executeBrokerRecover)
	))
}
check FaultTolerantKafkaEventuallyRecoversAfterCrash for 4


/**
 * An event can only be read after it has been pushed/published
 *
 * RESULT: 
 * Executing "Check EventCanOnlyBeReadAfterBeingPushed for 2"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=2 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..10 steps. 373519 vars. 6060 primary vars. 1072001 clauses. 20365ms.
 * No counterexample found. Assertion may be valid. 967ms.
 */
assert EventCanOnlyBeReadAfterBeingPushed {
	-- Any behaviour with an initially empty cluster (without any events)
	(kafkaFaultTolerantBehavior[2] or kafkaSimpleBehavior[2]) and (no getAllEventsInCluster[Kafka]) implies (
		-- If an event was read, it should have been pushed in the past
		all p: TopicPartition, e: KafkaEvent | always ( eventReadFromPartition[e, p] implies once(eventPushedToPartition[e, p]) )
	)
}
check EventCanOnlyBeReadAfterBeingPushed for 2


/**
 * This asserts that events in the same partition can be read in the order that they were pushed in
 *
 * RESULT:
 * Executing "Check SequentialityWithinPartition for 2"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=2 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..10 steps. 561818 vars. 6475 primary vars. 1594236 clauses. 44003ms.
 * No counterexample found. Assertion may be valid. 1415ms.
 */
assert SequentialityWithinPartition {
	-- Any behaviour with an initially empty cluster (without any events)
	(kafkaFaultTolerantBehavior[2] or kafkaSimpleBehavior[2]) and (no getAllEventsInCluster[Kafka]) implies (
		all p: TopicPartition, disj e1, e2 : KafkaEvent | always (
			-- If e2 is read after e1
			( eventReadFromPartition[e2, p] and once(eventReadFromPartition[e1, p]) ) implies
			-- Then e2 must have been pushed after e1
			once (eventPushedToPartition[e2, p] and once(eventPushedToPartition[e1, p]) )
		)
	)
}
check SequentialityWithinPartition for 2

/**
 * This asserts that an events in two different partitions can only be read in the order it was pushed in
 * This assertion is expected to result in a counterexample.
 *
 * RESULT
 * Executing "Check SequentialityBetweenTwoPartitions for 4"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=4 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..7 steps. 1182682 vars. 12838 primary vars. 3635116 clauses. 870104ms.
 * Counterexample found. Assertion is invalid. 311630ms.
 */
assert SequentialityBetweenTwoPartitions {
	-- Any behaviour with an initially empty cluster (without any events)
	( (kafkaFaultTolerantBehavior[2] or kafkaSimpleBehavior[2]) and (no getAllEventsInCluster[Kafka]) ) implies (
		all disj p1, p2: TopicPartition, disj e1, e2 : KafkaEvent | always (
			-- If e2 is read from p2 after e1 is read from p1
			(eventReadFromPartition[e2, p2] and once(eventReadFromPartition[e1, p1])) implies
			-- Then e2 was pushed to p2, after e1 was pushed to p1
			once (eventPushedToPartition[e2, p2] and once(eventPushedToPartition[e1, p1]) )
		)
	)
}
check SequentialityBetweenTwoPartitions for 4

/******************************************************************************************************/