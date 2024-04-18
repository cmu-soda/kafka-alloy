open actions as ac
open invariants as iv

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
 * 1..2 steps. 71958 vars. 1574 primary vars. 203465 clauses. 604ms.
 * Counterexample found. Assertion is invalid. 146ms.
 * 
 * Executing "Check InvariantsStrictAlwaysSatisfiesWithSimpleKafka for 5"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=5 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..2 steps. 130928 vars. 2533 primary vars. 371781 clauses. 8004ms.
 * Counterexample found. Assertion is invalid. 260ms.
 */
assert InvariantsStrictAlwaysSatisfiesWithSimpleKafka {
  -- Counterexample is expected for this assertion
  kafkaSimpleBehavior[3] implies always(InvariantsStrict[Kafka])
}
/** Assertion #1 **/
check InvariantsStrictAlwaysSatisfiesWithSimpleKafka for 4
check InvariantsStrictAlwaysSatisfiesWithSimpleKafka for 5


/**
 * Asserts that Strict invariants satisfy for kafkaFaultTolerantBehavior
 * Assertion is expected to be invalid because broker is allowed to crash
 *
 * RESULT:
 * Executing "Check InvariantsStrictAlwaysSatisfiesWithFaultTolerantKafka for 4"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=4 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..3 steps. 208675 vars. 4514 primary vars. 611418 clauses. 7919ms.
 * Counterexample found. Assertion is invalid. 1509ms.
 *
 * Executing "Check InvariantsStrictAlwaysSatisfiesWithFaultTolerantKafka for 5"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=5 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..3 steps. 248112 vars. 4740 primary vars. 744755 clauses. 146943ms.
 * Counterexample found. Assertion is invalid. 3013ms.
 */
assert InvariantsStrictAlwaysSatisfiesWithFaultTolerantKafka {
  -- Counterexample is expected for this assertion
  kafkaFaultTolerantBehavior[3] implies always(InvariantsStrict[Kafka])
}
/** Assertion #2 **/
check InvariantsStrictAlwaysSatisfiesWithFaultTolerantKafka for 4
check InvariantsStrictAlwaysSatisfiesWithFaultTolerantKafka for 5

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
 *
 * RESULT:
 * Executing "Check SimpleKafkaPreservesInvariantsAfterCrash for 3"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=3 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..3 steps. 276739 vars. 6140 primary vars. 802769 clauses. 542ms.
 * Counterexample found. Assertion is invalid. 93ms.
 *
 * Executing "Check SimpleKafkaPreservesInvariantsAfterCrash for 4"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=4 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..3 steps. 136323 vars. 2940 primary vars. 390030 clauses. 3072ms.
 * Counterexample found. Assertion is invalid. 246ms.
 */
assert SimpleKafkaPreservesInvariantsAfterCrash {
  kafkaSimpleBehavior[3] implies always(InvariantsAfterCrash[Kafka])
}
/** Assertion #3 **/
check SimpleKafkaPreservesInvariantsAfterCrash for 3
check SimpleKafkaPreservesInvariantsAfterCrash for 4


/**
 * kafkaFaultTolerantBehavior[3] ensures that a broker recovers after it crashes
 * Therefore, assertion holds because at least 2 replicas are always maintained
 *
 * RESULT:
 * Executing "Check FaultTolerantKafkaWithThreeReplicasPreservesInvariantsAfterCrash for 3"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=3 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..10 steps. 553375 vars. 12735 primary vars. 1683485 clauses. 51487ms.
 * No counterexample found. Assertion may be valid. 30632ms.
 * 
 * Executing "Check FaultTolerantKafkaWithThreeReplicasPreservesInvariantsAfterCrash for 4 but 9 steps"
 * Solver=sat4j Steps=1..9 Bitwidth=4 MaxSeq=4 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..9 steps. 917281 vars. 19242 primary vars. 2825093 clauses. 3327452ms.
 * No counterexample found. Assertion may be valid. 186673ms.
 *
 * Executing "Check FaultTolerantKafkaWithThreeReplicasPreservesInvariantsAfterCrash for 3"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=3 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..10 steps. 553375 vars. 12735 primary vars. 1683485 clauses. 57519ms.
 * No counterexample found. Assertion may be valid. 18325ms.
 *
 * Executing "Check FaultTolerantKafkaWithThreeReplicasPreservesInvariantsAfterCrash for 4 but 6 steps"
 * Solver=sat4j Steps=1..6 Bitwidth=4 MaxSeq=4 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..6 steps. 442483 vars. 9354 primary vars. 1349532 clauses. 928091ms.
 * No counterexample found. Assertion may be valid. 1868237ms.
 */
assert FaultTolerantKafkaWithThreeReplicasPreservesInvariantsAfterCrash {
  kafkaFaultTolerantBehavior[3] implies always(InvariantsAfterCrash[Kafka])
}
/** Assertion #4 -> Valid **/
check FaultTolerantKafkaWithThreeReplicasPreservesInvariantsAfterCrash for 3
check FaultTolerantKafkaWithThreeReplicasPreservesInvariantsAfterCrash for 4 but 6 steps

/**
 * The following assertion does not hold because replication of 2 would
 * leave no backup in case a broker goes down
 * This assertion is expected to give a counterexample
 *
 * RESULT:
 * Executing "Check FaultTolerantKafkaWithTwoReplicasPreservesInvariantsAfterCrash for 4"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=4 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..3 steps. 413126 vars. 9080 primary vars. 1209792 clauses. 24759ms.
 * Counterexample found. Assertion is invalid. 854ms.
 *
 * Executing "Check FaultTolerantKafkaWithTwoReplicasPreservesInvariantsAfterCrash for 5"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=5 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..3 steps. 247536 vars. 4740 primary vars. 743414 clauses. 356573ms.
 * Counterexample found. Assertion is invalid. 692ms.
 */
assert FaultTolerantKafkaWithTwoReplicasPreservesInvariantsAfterCrash {
  kafkaFaultTolerantBehavior[2] implies always(InvariantsAfterCrash[Kafka])
}
/** Assertion #5 **/
check FaultTolerantKafkaWithTwoReplicasPreservesInvariantsAfterCrash for 4
check FaultTolerantKafkaWithTwoReplicasPreservesInvariantsAfterCrash for 5

/**
 * kafkaFaultTolerantBehavior ensures that a broker recovers after it crashes, leading
 * to satisfaction of replication factor criteria.
 * Therefore this assertion holds.
 *
 * RESULT:
 * Executing "Check BrokerRecoverAfterCrashPreservesInvariantsStrict for 3"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=3 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..10 steps. 1031753 vars. 21815 primary vars. 3113952 clauses. 15829ms.
 * No counterexample found. Assertion may be valid. 145ms.
 *
 * Executing "Check BrokerRecoverAfterCrashPreservesInvariantsStrict for 4 but 9 steps"
 * Solver=sat4j Steps=1..9 Bitwidth=4 MaxSeq=4 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..9 steps. 1032654 vars. 19242 primary vars. 3220587 clauses. 604674ms.
 * No counterexample found. Assertion may be valid. 428819ms.
 */
assert BrokerRecoverAfterCrashPreservesInvariantsStrict {
  kafkaFaultTolerantBehavior[3] implies always (
    -- After broker failure, InvariantsAfterCrash satisfies until broker recovers
    (executeBrokerCrash implies after(InvariantsAfterCrash[Kafka] until executeBrokerRecover))
    
    -- Strict invariants start to satisfy once a broker recovers
    and (executeBrokerRecover implies after(InvariantsStrict[Kafka]))
  )
}
/** Assertion #6 -> Valid **/
check BrokerRecoverAfterCrashPreservesInvariantsStrict for 3
check BrokerRecoverAfterCrashPreservesInvariantsStrict for 4 but 9 steps


/**
 * If broker never goes down, Strict invariants satisfy for either of the two behaviors:
 * kafkaSimpleBehavior or kafkaFaultTolerantBehavior
 *
 * RESULT:
 * Executing "Check NeverBrokerCrashPreservesStrictInvariants for 3"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=3 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..10 steps. 554253 vars. 12735 primary vars. 1685883 clauses. 139380ms.
 * No counterexample found. Assertion may be valid. 7738ms.
 *
 * Executing "Check NeverBrokerCrashPreservesStrictInvariants for 4 but 6 steps"
 * Solver=sat4j Steps=1..6 Bitwidth=4 MaxSeq=4 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..6 steps. 443171 vars. 9354 primary vars. 1351462 clauses. 5790138ms.
 * No counterexample found. Assertion may be valid. 5816899ms.
 */
assert NeverBrokerCrashPreservesStrictInvariants {
  (kafkaSimpleBehavior[2] or kafkaFaultTolerantBehavior[2]) implies
    ((not eventually(executeBrokerCrash)) implies always(InvariantsStrict[Kafka]))
}
/** Assertion #7 -> Valid **/
check NeverBrokerCrashPreservesStrictInvariants for 3
check NeverBrokerCrashPreservesStrictInvariants for 4 but 6 steps


/**
 * LIVENESS: Everytime a broker crashes, it must recover at some point in the future
 * and must not crash again before that recovery
 *
 * RESULT: 
 * Executing "Check FaultTolerantKafkaEventuallyRecoversAfterCrash for 4"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=4 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..10 steps. 2413807 vars. 50805 primary vars. 7442066 clauses. 39830ms.
 * No counterexample found. Assertion may be valid. 372ms.
 *
 * Executing "Check FaultTolerantKafkaEventuallyRecoversAfterCrash for 5 but 9 steps"
 * Solver=sat4j Steps=1..9 Bitwidth=4 MaxSeq=5 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..9 steps. 1714547 vars. 31203 primary vars. 5452569 clauses. 68395ms.
 * No counterexample found. Assertion may be valid. 381ms.
 */
assert FaultTolerantKafkaEventuallyRecoversAfterCrash {
  kafkaFaultTolerantBehavior[3] implies always (executeBrokerCrash implies (
    -- Eventually recover
    eventually(executeBrokerRecover)

    -- No crash before recovery
    and after((not executeBrokerCrash) until executeBrokerRecover)
  ))
}
/** Assertion #8 -> Valid **/
check FaultTolerantKafkaEventuallyRecoversAfterCrash for 4
check FaultTolerantKafkaEventuallyRecoversAfterCrash for 5 but 9 steps


/**
 * An event can only be read after it has been pushed/published
 *
 * RESULT: 
 * Executing "Check EventCanOnlyBeReadAfterBeingPushed for 2"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=2 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..10 steps. 371204 vars. 5900 primary vars. 1088532 clauses. 24650ms.
 * No counterexample found. Assertion may be valid. 2450ms.
 *
 * Executing "Check EventCanOnlyBeReadAfterBeingPushed for 3"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=3 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..10 steps. 3274378 vars. 63840 primary vars. 10079025 clauses. 103479ms.
 * No counterexample found. Assertion may be valid. 25209ms.
 *
 * Executing "Check EventCanOnlyBeReadAfterBeingPushed for 4 but 9 steps"
 * Solver=sat4j Steps=1..9 Bitwidth=4 MaxSeq=4 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..9 steps. 1385712 vars. 19521 primary vars. 4359482 clauses. 3387925ms.
 * No counterexample found. Assertion may be valid. 5073704ms.
 */
assert EventCanOnlyBeReadAfterBeingPushed {
  -- Any behaviour with an initially empty cluster (without any events)
  (kafkaFaultTolerantBehavior[2] or kafkaSimpleBehavior[2]) and (no getAllEventsInCluster[Kafka]) implies (
    -- If an event was read, it should have been pushed in the past
    all p: TopicPartition, e: KafkaEvent | always ( eventReadFromPartition[e, p] implies once(eventPushedToPartition[e, p]) )
  )
}
/** Assertion #9 -> Valid **/
check EventCanOnlyBeReadAfterBeingPushed for 3
check EventCanOnlyBeReadAfterBeingPushed for 4 but 9 steps

/**
 * This asserts that events in the same partition can be read in the order that they were pushed in
 *
 * RESULT:
 * Executing "Check SequentialityWithinPartition for 2"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=2 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..10 steps. 559312 vars. 6315 primary vars. 1626247 clauses. 53276ms.
 * No counterexample found. Assertion may be valid. 1402ms.
 * 
 * Executing "Check SequentialityWithinPartition for 3"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=3 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..10 steps. 1207762 vars. 13470 primary vars. 3693935 clauses. 172644ms.
 * No counterexample found. Assertion may be valid. 22521ms.
 *
 * Executing "Check SequentialityWithinPartition for 4 but 9 steps"
 * Solver=sat4j Steps=1..9 Bitwidth=4 MaxSeq=4 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..9 steps. 1888051 vars. 19899 primary vars. 5969660 clauses. 1089454ms.
 * No counterexample found. Assertion may be valid. 2640708ms.
 */
assert SequentialityWithinPartition {
  -- Any behaviour with an initially empty cluster (without any events)
  (kafkaFaultTolerantBehavior[2] or kafkaSimpleBehavior[2]) and (no getAllEventsInCluster[Kafka]) and #Consumer=1 implies (
    all p: TopicPartition, disj e1, e2 : KafkaEvent | always (
      -- If e2 is read after e1
      ( eventReadFromPartition[e2, p] and once(eventReadFromPartition[e1, p]) ) implies
      -- Then e2 must have been pushed after e1
      once (eventPushedToPartition[e2, p] and once(eventPushedToPartition[e1, p]) )
    )
  )
}
/** Assertion #10 -> Valid **/
check SequentialityWithinPartition for 3
check SequentialityWithinPartition for 4 but 9 steps

/**
 * This asserts that an events in two different partitions can only be read in the order it was pushed in
 * This assertion is expected to result in a counterexample.
 *
 * Executing "Check SequentialityBetweenTwoPartitions for 4"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=4 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..7 steps. 1207073 vars. 12726 primary vars. 3794187 clauses. 110647ms.
 * Counterexample found. Assertion is invalid. 12711ms.
 * 
 * Executing "Check SequentialityBetweenTwoPartitions for 5"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=5 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..7 steps. 2140208 vars. 20342 primary vars. 6863914 clauses. 286566ms.
 * Counterexample found. Assertion is invalid. 46677ms.
 */
assert SequentialityBetweenTwoPartitions {
  -- Any behaviour with an initially empty cluster (without any events)
  ( (kafkaFaultTolerantBehavior[2] or kafkaSimpleBehavior[2]) and (no getAllEventsInCluster[Kafka]) ) and #Consumer=1 implies (
    all disj p1, p2: TopicPartition, disj e1, e2 : KafkaEvent | always (
      -- If e2 is read from p2 after e1 is read from p1
      (eventReadFromPartition[e2, p2] and once(eventReadFromPartition[e1, p1])) implies
      -- Then e2 was pushed to p2, after e1 was pushed to p1
      once (eventPushedToPartition[e2, p2] and once(eventPushedToPartition[e1, p1]) )
    )
  )
}
/** Assertion #11 **/
check SequentialityBetweenTwoPartitions for 4
check SequentialityBetweenTwoPartitions for 5

/******************************************************************************************************/
