open actions
open invariants


/**
 * RESULTS of Execute All:
 *
 * 9 commands were executed. The results are:
 *  #1: Instance found.findSomeReadEventInstance is consistent.
 *  #2: No counterexample found. readEventPreservesInvariants may be valid.
 *  #3: Instance found.findSomePushEventInstance is consistent.
 *  #4: No counterexample found. pushEventPreservesInvariants may be valid.
 *  #5: Instance found.findSomeBrokerCrashInstance is consistent.
 *  #6: Counterexample found. onceBrokerCrashPreservesInvariantsStrict is invalid.
 *  #7: No counterexample found. onceBrokerCrashPreservesInvariantsAfterCrash may be valid.
 *  #8: Instance found. findSomeBrokerRecoverInstance is consistent.
 *  #9: No counterexample found. brokerRecoverPreservesInvariantsAfterRecover may be valid.
 * 
 * NOTE: Counterexample in #6 is expected, please look at the comments above
 *       onceBrokerCrashPreservesInvariantsStrict to see why.
 */
/*******************************
 * Valid Initial states of Kafka
 *******************************/
pred Init[repFactor: Int] {
  Kafka.replicationFactor = repFactor
  InvariantsStrict[Kafka]
}

/**
 * Broker won't recover if InvariantsStrict satisfies in initial state
 * Instead InvariantsAfterCrash should satisfy before brokerRecover
 */
pred InitBeforeRecover[repFactor: Int] {
  Kafka.replicationFactor = repFactor
  InvariantsAfterCrash[Kafka]
}




/***************************
 * Verify Action: readEvent
 ****************************/
/**
 * Used in readEventBehavior fact to assert that this behavior will preserve invariant
 */
pred readEventBehavior[repFactor: Int] {
  -- Initial state --
  ---------------
  Init[repFactor]

  -- Non-deterministic readEvent transition --
  ---------------------------------------
  always (executeReadEvent or doNothing)
}

/**
 * This finds a simple instance to visually see the transition
 */
run findSomeReadEventInstance {
  Init[2] and some Kafka.zookeeper.topics.partitions.leader.events
  executeReadEvent and after(doNothing)
} for 6

/**
 * This asserts that the invariants are preserved for all state in the trace,
 * the behavior of which is defined in readEventBehavior
 */
assert readEventPreservesInvariants {
  -- Set runMode to modify behavior
  readEventBehavior[3] implies always(InvariantsStrict[Kafka])
}
check readEventPreservesInvariants for 4






/***************************
 * Verify Action: pushEvent
 ****************************/

/**
 * This defines the behavior of this model
 * Here a single transition of pushEvent takes place
 * This will be used to verify if the transition pushEvent preserved invariants
 */
pred pushEventBehavior[repFactor : Int] {
  -- Initial state --
  ---------------
  Init[repFactor]

  -- Single pushEvent transition --
  ----------------------------
  always(executePushEvent or doNothing)
}

/**
 * This finds a simple instance to visually see the pushEvent transition
 */
run findSomePushEventInstance {
  Init[2] and some Kafka.zookeeper.topics.partitions.leader.events
  executePushEvent and after(doNothing)
} for 4

/**
 * This asserts that the invariants are preserved for all state in the trace,
 * the behavior of which is defined in pushEventBehavior
 */
assert pushEventPreservesInvariants {
  -- Set runMode to modify behavior
  pushEventBehavior[3] implies always(InvariantsStrict[Kafka])
}
check pushEventPreservesInvariants for 3
  






/***************************
 * Verify Action: brokerCrash
 ****************************/

/**
 * This pred defines the behavior of this model
 * runMode = 0 is set in the run command to modify behavior to execute brokerCrash only once for
 * sake of visualization. runMode = 1 is set in the assertion to modify behavior where brokerCrash
 * occurs or nothing occurs for infinite steps
 */
pred brokerCrashBehavior[repFactor: Int] {
  -- Initial state --
  ---------------
  Init[repFactor]

  -- Transition --
  --------------
  -- Single step transition  
  executeBrokerCrash
}

/**
 * This finds a simple instance to visually see the transition
 */
run findSomeBrokerCrashInstance {
  Init[3] and some Kafka.zookeeper.topics.partitions.leader.events
  executeBrokerCrash and after(doNothing)
} for 6

/**
 * This asserts that the strict invariants are preserved for all state in the trace,
 * Following a single brokerCrash
 */
assert onceBrokerCrashPreservesInvariantsStrict {
  brokerCrashBehavior[3] implies after(InvariantsStrict[Kafka])
}
check onceBrokerCrashPreservesInvariantsStrict for 3

/**
 * This asserts that the relaxed invariants are preserved for all state in the trace,
 * Following a single brokerCrash
 */
assert onceBrokerCrashPreservesInvariantsAfterCrash {
  -- Set runMode to modify behavior
  brokerCrashBehavior[3] implies after (InvariantsAfterCrash[Kafka])
}
check onceBrokerCrashPreservesInvariantsAfterCrash for 4

/**
 * This asserts that the relaxed invariants are preserved for all state in the trace,
 * Following a single brokerCrash
 */
assert onceBrokerCrashPreservesInvariantsAfterCrashForReplicationTwo {
  -- Set runMode to modify behavior
  brokerCrashBehavior[2] implies after (InvariantsAfterCrash[Kafka])
}
check onceBrokerCrashPreservesInvariantsAfterCrashForReplicationTwo for 4




/*******************************
 * Verify Action: brokerRecover
 ********************************/
/**
 * This PRED defines the behavior of this model
 * runMode = 0 is set in the run command to modify behavior to execute brokerRecover only once for
 * sake of visualization. runMode = 1 is set in the assertion to modify behavior where brokerRecover
 * occurs or nothing occurs for infinite steps
 */
pred brokerRecoverBehavior[repFactor: Int] {
  -- Initial state --
  ---------------
  InitBeforeRecover[repFactor]

  -- Transition --
  --------------
  -- Single step transition
  executeBrokerRecover
  -- Later steps
  always(executeBrokerRecover or doNothing)
}

/**
 * This finds a simple instance to visually see the transition
 */
run findSomeBrokerRecoverInstance {
  InitBeforeRecover[3] and some Kafka.zookeeper.topics.partitions.leader.events
  executeBrokerRecover and after(doNothing)
} for 4

/**
 * This asserts that the invariants are preserved for all states in the trace,
 * the behavior of which is defined in fact 
 * executeBrokerRecoverActionOnceAndThenDoWhatever
 */
assert brokerRecoverPreservesInvariantsAfterRecover {
  brokerRecoverBehavior[3] implies 
    (InvariantsAfterCrash[Kafka] and after(always(InvariantsStrict[Kafka])))
}
check brokerRecoverPreservesInvariantsAfterRecover for 4

