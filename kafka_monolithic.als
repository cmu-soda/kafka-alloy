open util/relation

/***************
 * INVARIANTS
 ***************/

/**
 * Invariants that should satisfy when no broker has crashed
 * - Requires exact number of replicas of partitions as configured for the
 *    cluster
 */
pred InvariantsStrict[k : Kafka] {
  InvariantsAfterCrash[k]
  topicPartitionMustSatisfyReplicationFactor[k]
}

/**
 * Relaxed invariant that should satisfy after a broker crashes
 * - This invariant does not require exact number of replicas of partitions
 *   as configured for the cluster
 * - This invariant does require at least one replica (as backup) to 
 *    exist at all times
 */
pred InvariantsAfterCrash[k : Kafka] {
  topicPartitionMustHaveOneLeader[k]
  allTopicReplicasInBrokers[k]
  topicSubscriptionsMustBelongToCluster[k]
  partitionReplicasOnDifferentBrokers[k]
  someTopicPartitionReplicaPresentInCluster[k]
  followersMustBeInSyncWithLeader[k]
  eventsMustStaySecureInsideTheCluster[k]
  topicPartitionMustHaveBackups[k] -- At least one backup should exist
  consumersCanBeAssignedToParititonsInTheCluster[k]
}

/**
 * Each partition should have exactly one leader replica
 */
pred topicPartitionMustHaveOneLeader[k : Kafka] {
  all k: Kafka, p : k.zookeeper.topics.partitions | one p.leader
}

/**
 * Each partition should have backup replicas
 */
pred topicPartitionMustHaveBackups[k : Kafka] {
  all p : k.zookeeper.topics.partitions | #p.(leader + followers) > 1
}

/**
 * Each partition should have total replicas equal to Kafka.replicationFactor
 */
pred topicPartitionMustSatisfyReplicationFactor[k : Kafka] {
  all p : k.zookeeper.topics.partitions |  #p.(leader+followers) = k.replicationFactor
}

/**
 * All partition replicas of topics belonging to the cluster should be present in Brokers
 * of the cluster
 */
pred allTopicReplicasInBrokers[k : Kafka] {
  getPartitionReplicas[k.zookeeper.topics.partitions] = k.zookeeper.brokers.replicasInBroker
}

/**
 * Topics subscribed by consumer groups must be present in the kafka cluster
 */
pred topicSubscriptionsMustBelongToCluster[k:Kafka] {
  k.consumer_groups.subscribedTo in k.zookeeper.topics
}

/**
 * No two replicas of a partition can be present in the same broker
 */
pred partitionReplicasOnDifferentBrokers[k : Kafka] {
  all p : k.zookeeper.topics.partitions |
    all disj r1, r2 : getPartitionReplicas[p] | disj[r1.~replicasInBroker, r2.~replicasInBroker]
}

/**
 * For each partition, one or more partition replicas must be present in the 
 * cluster brokers at all times
 */
pred someTopicPartitionReplicaPresentInCluster[k : Kafka] {
  all p: k.zookeeper.topics.partitions | 
    some (getPartitionReplicas[p] & k.zookeeper.brokers.replicasInBroker)
}

/**
 * All events saved in leader replica must also be present in follower replicas for a
 * given partition
 */
pred followersMustBeInSyncWithLeader[k : Kafka] {
  all p : k.zookeeper.topics.partitions | 
    let l = p.leader | all f : p.followers | f.events = l.events
}

/**
 * Events inside a cluster cannot belong in a broker other than brokers of the cluster
 */
pred eventsMustStaySecureInsideTheCluster[k : Kafka] {
  all e: getAllEventsInCluster[k] | getBrokersContainingEvent[e] in k.zookeeper.brokers
}

/**
 * Consumers can only be assigned to partitions belonging to topics of the cluster.
 */
pred consumersCanBeAssignedToParititonsInTheCluster[k : Kafka] {
  all k : Kafka, c : k.consumer_groups.consumers | c.assignedTo in k.zookeeper.topics.partitions
}



/**********************
 * HELPER FUNCTIONS
 **********************/

/**
 * Returns a set of replicas of a TopicPartition
 *
 * @p : TopicPartition instance
 * @return : Replicas of p
 */
fun getPartitionReplicas[p : TopicPartition] : PartitionReplica {
  {p.leader + p.followers}
}

/**
 * Fetches all events present in the kafka cluster
 *
 * @k : State of Kafka cluster
 * @return : Set of KafkaEvent instances contained in the cluster
 */
fun getAllEventsInCluster[k : Kafka] : KafkaEvent {
  k.zookeeper.topics.partitions.leader.events.elems
}

/**
 * Fetches brokers that contain a KafkaEvent
 *
 * @e : KafkaEvent instance
 * @return : set of brokers that contain e
 */
fun getBrokersContainingEvent[e : KafkaEvent] : Broker{
  (events.e.Int).~replicasInBroker
}

/**
 * Fetches the set of partitions that have insufficient number of replicas
 *
 * @k : State of Kafka cluster
 * @return : Set of partitions that require recovery
 */
fun partitionsRequiringRecovery[k : Kafka] : TopicPartition {
  {p : k.zookeeper.topics.partitions | #p.(leader + followers) < k.replicationFactor}
}


/***************
 * SIGNATURES
 ***************/

/* Kafka instance representing the state of the Cluster
 * This model considers a single Kafka cluste */
one sig Kafka {
  -- Fix the number of replicas that should be present
  -- for each partition
  replicationFactor: one Int,
  -- One unshared zookeeper to manage cluster metadata
  zookeeper: disj one ZooKeeper,
  -- Consumer groups should not be shared across multiple clusters
  consumer_groups: disj set ConsumerGroup,
  -- Producers should not be shared across multiple clusters
  producers: disj set Producer
}

/* Zookeeper is responsible for managing metadata about the cluster */
sig ZooKeeper {
  -- Cluster must contain at least one broker
  -- Broker not shared with another cluster
  var brokers: disj some Broker,
  -- Cluster can contain 0 or more topics
  -- A topic cannot belong to two clusters (zookeepers)
  topics: disj set Topic
} {
  -- Zookeeper only associated with Kafka
  ZooKeeper = Kafka.zookeeper
}

/* A Broker is a single server in a cluster of servers which store 
 * replicas of Topic partitions */
sig Broker {
  -- No two brokers can have the same replica instance
  var replicasInBroker: disj set PartitionReplica
}

/* Topic is the entitity that stores streamed data 
points in its partitions */
sig Topic {
  -- A topic should have at least one partition
  -- No two topics can share the same partition
  partitions: disj some TopicPartition
} {
  -- Each Topic should be associated to a cluster
  Topic = ZooKeeper.topics
}

/* Represents a partition of a topic which stores 
 * published events in a sequential manner */
sig TopicPartition {
  -- At-most one Leader that cannot be shared 
  -- by any other partition
  var leader: disj lone PartitionReplica,
  -- No two TopicPartitions should share a FollowerReplica
  var followers: disj set PartitionReplica,
} {
  -- A replica can't have both leader and follower role
  disj[leader, followers]
  -- TopicPartitions must always be associated with Topics
  TopicPartition = Topic.partitions
}

/* A partition replica is associated with a TopicPartition
 * Replicas store KafkaEvent instances */
sig PartitionReplica {
  -- Ordered sequence of KafkaEvents
  var events: seq KafkaEvent,
} {
  -- Every event must be unique
  !events.hasDups[]
  -- replicas cannot be shared between two partitions
  -- E.g. A leader of one partition cannot be follower of another.
  all p : TopicPartition | 
    disj[p.(leader + followers), 
      (TopicPartition - p).(leader + followers)]
}

/* KafkaEvent represents a message */
sig KafkaEvent {} {
  -- An event cannot belong to two partitions
  all p : TopicPartition | 
    disj[p.(leader+followers).events.elems, 
      (TopicPartition - p).(leader+followers).events.elems]
}

/* Producer publishes KafkaEvents to a Partition */
sig Producer {} {
  -- Producer always associated with a cluster
  Producer = Kafka.producers
}

/* A Consumer client application */
abstract sig Consumer {
  -- A consumer can be assigned to multiple partitions
  -- Multiple consumers can be assigned to a partition
  assignedTo: set TopicPartition
}

/* A ConsumerGroup represents a group of Consumer instances
 * It subscribes to certain topics and maintains 
 * Consumer -> TopicPartition assignment
 * and TopicPartition -> Int offset data */
sig ConsumerGroup {
  -- No two groups can have the same consumer
  consumers: disj some Consumer,

  -- A Consumer Group subscribes to a set of Topics
  -- Many consumer groups can subscribe to the same Topic
  subscribedTo: set Topic,

  -- Maintain the index of the TopicPartition that it last read
  var offsets: TopicPartition -> {i : Int | i >= 0}, 

  -- Consumers are assigned to partitions
  assignments: Consumer -> TopicPartition
} {
  -- Group must be associated to a kafka cluster
  ConsumerGroup = Kafka.consumer_groups

  -- CG keeps track of last read index of partitions of subscribed topics 
  -- The offset cannot be greater than the number of events in the parition.
  all p : subscribedTo.partitions | 
    one offsets[p] and offsets[p] <= p.leader.events.lastIdx[]

  -- CG must keep partition assignment data
  assignments = consumers <: assignedTo -- domain restriction
  
  -- CG must assign partition of subscribed topics to consumers
  consumers.assignments = subscribedTo.partitions
    
  -- No two consumers in consumer group should be
  -- assigned to the same partition
  all disj c1, c2 : consumers | disj[c1.assignedTo, c2.assignedTo]
  
  -- No consumer in consumer group should be idle
  all c : consumers | some c.assignedTo
}

/***************
 * ACTIONS
 ***************/

/*********************************** WRAPPED ACTIONS ******************************/

pred eventReadFromPartition[e : KafkaEvent, p : TopicPartition] {
  some k: Kafka, c : Consumer | readEvent[k, c, e, p]
}

pred eventPushedToPartition[e : KafkaEvent, p : TopicPartition] {
  some k: Kafka, prod : Producer | pushEvent[k, prod, e, p]
}

pred executeReadEvent {
  some k: Kafka, c: Consumer, e : KafkaEvent, p : TopicPartition | readEvent[k, c, e, p]
}

pred executePushEvent {
  some k: Kafka, prod : Producer, e : KafkaEvent, p : TopicPartition | pushEvent[k, prod, e, p]
}

pred executeBrokerCrash {
  some k: Kafka, b : Broker | brokerCrash[k, b]
}

pred executeBrokerRecover {
  some k: Kafka, b : Broker | brokerRecover[k, b]
}

pred doSomething {
  executeReadEvent or executePushEvent or executeBrokerCrash or executeBrokerRecover
}

pred doNothing {
  offsets' = offsets
  events' = events
  brokers' = brokers
  leader' = leader
  followers' = followers
  replicasInBroker' = replicasInBroker
}
/****************************************************************************************/



/************************************ READ EVENT *************************************/

/**
 * Transition where a consumer reads an event from its assigned partition
 * As a result the offset corresponding to this partition saved in corresponding
 * consumer group, must be incremented
 *
 * @k : Kafka cluster state
 * @c : Consumer that reads the event
 * @e : The KafkaEvent being read
 * @p : The partition being read from
 */
pred readEvent[k: Kafka, c_multiple : Consumer, e: KafkaEvent, p : TopicPartition] {
  -- Pre --
  --------
  all c: c_multiple | consumerCanReadEventFromPartition[k, c, e, p]

  -- Post --
  ---------
  -- @cg: ConsumerGroup containing the consumer
  -- Offset for the partition should be increased in Consumer c's ConsumerGroup
  all c: c_multiple | let cg = c.~consumers | cg.offsets'[p] = cg.offsets[p].add[1]
  
  -- Frame --
  ----------
  readEventFrame[k, c_multiple, e, p]
}

/**
 * Predicate that checks if an Event instance is readable by a consumer from a Partition
 *
 * @k : Kafka cluster state
 * @c : Consumer that reads the event
 * @e : The KafkaEvent being read
 * @p : The partition being read from
 */
pred consumerCanReadEventFromPartition[k: Kafka, c : Consumer, e: KafkaEvent, p : TopicPartition] {
  -- Basic Permissions Checks --
  --------------------------
  -- The cluster should be aware of Consumer c
  c in k.consumer_groups.consumers
  -- Consumer should be assigned to partition
  p in c.assignedTo

  -- Partition p should belong to cluster
  p in k.zookeeper.topics.partitions
  
  -- Event Position Check --
  -----------------------
  -- The Event e must be present at the index that is saved for the paritition in consumer's group
  -- @cg: ConsumerGroup containing the consumer
  let cg = c.~consumers | cg.offsets[p] = p.leader.events.indsOf[e]
}

/**
 * Predicate defining frame conditions for readEvent action
 *
 * @k : Kafka cluster state
 * @c : Consumer that reads the event
 * @e : The KafkaEvent being read
 * @p : The partition being read from
 */
pred readEventFrame[k: Kafka, c_mult : Consumer, e: KafkaEvent, p : TopicPartition] {
  -- Preserve Other Offsets --
  -------------------------
  -- Preserve domain of the 'offsets' relation
  dom[offsets.Int] = dom[offsets'.Int]
  
  -- @cg : ConsumerGroup of consumer
  let cgs = c_mult.~consumers | {
    -- All offsets corresponding to ConsumerGroup instances other than 'cg' should be unchanged
    all other_cg : dom[offsets.Int] - cgs | other_cg.offsets' = other_cg.offsets
    
    -- Offsets corresponding to TopicPartition instances other than 'p' should be unchanged in the current ConsumerGroup
    all cg: cgs | all other_p : dom[cg.offsets] - p | cg.offsets'[other_p] = cg.offsets[other_p]
  }
  
  -- Preserve unaffected variables
  readEventUnaffectedVariablesFrame
}

/**
 * A predicate used to preserve variables unaffected by readEvent action
 */
pred readEventUnaffectedVariablesFrame {
  events' = events
  brokers' = brokers
  leader' = leader
  followers' = followers
  replicasInBroker' = replicasInBroker
}

/****************************************************************************************/

/************************************* PUSH EVENT *************************************/
/**
 * Transition where a producer sends an event to its assigned partition
 * As a result the new event should be appended to the last index of events saved in leader
 * Followers should sync up with the leader as well
 *
 * @k : Kafka cluster state
 * @prod : Producer that sends the event
 * @e : KafkaEvent being sent
 * @p : The partition being written into
 */
pred pushEvent[k : Kafka, prod : Producer, e: KafkaEvent, p : TopicPartition] {
  -- Pre --
  --------
    canProducerPushEvent[k, prod, e, p]

  -- Post --
  ---------
    -- add KafkaEvent e to the leader PartitionReplica of p
    p.leader.events' = p.leader.events.add[e]

  -- Follower replicas should sync up
    sync[p.leader, p.followers]
  
  -- Frame --
  ----------
    pushEventFrame[p]
}

/**
 * This predicate checks if the Producer has the required privileges to publish a new event
 * e to the TopicPartition p
 *
 * @k : Kafka cluster state
 * @prod : Producer that sends the event
 * @e : KafkaEvent being sent
 * @p : The partition being written into
 */
pred canProducerPushEvent[k : Kafka, prod : Producer, e: KafkaEvent, p : TopicPartition] {
  -- Partition p should belong to cluster
  p in k.zookeeper.topics.partitions

  -- Producer prod should be confugured in the cluster
  prod in k.producers

  -- KafkaEvent e should not exist anywhere in the cluster pre-state
  e not in k.zookeeper.topics.partitions.leader.events.elems

  -- Event not already belonging to a internal/external PartitionReplica
  no events.e
}

/**
 * Syncs up data in all follower PartitionReplica instances with the leader PartitionReplica
 */
pred sync[leader_replica, follower_replicas: PartitionReplica] {
  all f : follower_replicas | f.events' = leader_replica.events'
}

/**
 * Frame conditions that should be satisfied for a partition
 * in which an event was published
 */
pred pushEventFrame[p : TopicPartition] {
  -- Events in other partitions should stay the same
  all r : PartitionReplica - p.(leader + followers) | r.events' = r.events

  -- Preserve unaffected state variables
  pushEventUnaffectedVariablesFrame
}

/**
 * A predicate that preserves variables unaffected by pushEvent
 */
pred pushEventUnaffectedVariablesFrame {
  offsets' = offsets
  brokers' = brokers
  leader' = leader
  followers' = followers
  replicasInBroker' = replicasInBroker
}
/****************************************************************************************/



/************************************ BROKER CRASH *************************************/

/**
 * Transition where a broker goes down
 * As a result the broker is removed from the cluster
 *
 * @k : Kafka cluster state
 * @b : Broker that goes down
 */
pred brokerCrash[k: Kafka, b : Broker] {
  -- Pre --
  --------
    -- broker must belong to cluster pre-state
    b in k.zookeeper.brokers

  -- leaders/followers lost after crash
  let leader_replicas = b.replicasInBroker & ran[leader] |
  let follower_replicas = b.replicasInBroker & ran[followers] | {
  -- Post --
  ---------  
    -- remove broker from cluster
    --brokers' = brokers - (brokers :> b)
    k.zookeeper.brokers' = k.zookeeper.brokers - b

    -- Elect new leaders for Partitions who lost their leaders when broker crashed
    electNewLeaders[leader_replicas]

    -- Delink followers for TopicPartitions who lost their followers
    delinkFollowers[follower_replicas]

    -- Remove all events that were saved in lost replicas
    events' = events - ((leader_replicas + follower_replicas) <: events) -- domain restriction

  -- Frame --
  -----------
    brokerCrashFrame[leader_replicas, follower_replicas]
  }
}

/**
 * Given old leaders, elect a new leader from the corresponding TopicPartition's
 * list of followers
 * 
 * @l_replicas : List of pre-state leaders
 */
pred electNewLeaders[l_replicas: PartitionReplica] {
  all lr : l_replicas | let p = leader.lr | one new_l :  p.followers {
    -- Assign new_l as the new leader
    p.leader' = new_l

    -- Remove new_l from list of followers
    p.followers' = p.followers - new_l
  }
}

/**
 * A set of followers must be removed from the replicas present
 */
pred delinkFollowers[f_replicas : PartitionReplica] {
  -- Remove followers from partitions who lost it
  all fr: f_replicas | let p = followers.fr | {
    p.followers' = p.followers - fr
  }
}

/**
 * Predicate defining frame conditions for brokerCrash action
 *
 * @ leader_replicas : PartitionReplica instances that were assigned as leaders
 */
pred brokerCrashFrame[leader_replicas, follower_replicas : PartitionReplica] {
  -- Domain of leader should not change as TopicPartitions stay the same
  dom[leader'] = dom[leader]
  -- Domain of follower should be the one before minus the partitions that lost followers
  dom[followers'] = dom[followers - (followers :> follower_replicas)]
  
  -- Partitions who did not lose their leader/followers should have the same 
  -- leaders/followers in post-state
  all other_p : dom[leader] - leader.leader_replicas | 
    other_p.leader' = other_p.leader

  all other_p : dom[followers] - followers.follower_replicas | 
    other_p.followers' = other_p.followers

  -- Other required frame conditions are satisfied in the brokerCrash post-state actions
  brokerCrashUnaffectedVariablesFrame
}

/**
 * A predicate used to preserves variables unaffected by brokerCrash
 */
pred brokerCrashUnaffectedVariablesFrame {
  offsets' = offsets
  replicasInBroker' = replicasInBroker
}
/****************************************************************************************/


/************************************ BROKER RECOVER *************************************/

/**
 * Transition where a new broker comes up
 *
 * @k : Kafka cluster state
 * @b : Broker added
 */
pred brokerRecover[k: Kafka, b : Broker] {
  -- Pre --
  --------
    brokerCanBeAdded[k, b]

  -- Post --
  ---------
  -- Add the new broker to the cluster
  // brokers' = brokers + (k.zookeeper -> b)
  k.zookeeper.brokers' = k.zookeeper.brokers + b

  -- new server b should be added to the domain of replicasInBroker 
  dom[replicasInBroker'] = dom[replicasInBroker] + b

  -- create new followers to be put into the new broker
  let recover_partitions = partitionsRequiringRecovery[k] | {
    all rp : recover_partitions | let lr = rp.leader | one new_f : PartitionReplica {
      -- new_f doesn't exist in any broker in pre-state
      no replicasInBroker.new_f
      -- new_f contains no events in pre-state
      no new_f.events

      -- replicate events from leader
      new_f.events' = lr.events'

      -- link the new follower to the partition needing recovery
      rp.followers' = rp.followers + new_f

      -- save the partition in the new broker
      new_f in b.replicasInBroker'
    }

    -- Domain of events includes new replicas created (only followers were created)
    dom[events'.KafkaEvent] = dom[events.KafkaEvent] + recover_partitions.followers'

    -- Domain of followers should include recover_partitions which may not have had followers before
    dom[followers'] = dom[followers] + recover_partitions

    -- Replicas contained in the new broker should only be followers 
    -- that belong to the cluster
    b.replicasInBroker' in k.zookeeper.topics.partitions.followers'

  -- Frame --
  -----------
    brokerRecoverFrame[recover_partitions]
  }
}

/**
 * This is to check if a broker can be added to a particular state of Kafka
 * 
 * @k : Represents state of Kafka cluster
 * @b : The new broker to be added
 */
pred brokerCanBeAdded[k : Kafka, b : Broker] {
  -- new broker must not belong to cluster pre-state
  b not in k.zookeeper.brokers

  -- new broker should not contain any data in the pre-state
  no b.replicasInBroker.events

  -- The cluster should require recovery
  some partitionsRequiringRecovery[k]
}


/**
 * A predicate used to preserves variables unaffected by brokerCrash
 */
pred brokerRecoverUnaffectedVariablesFrame {
  leader' = leader
  offsets' = offsets
}

/**
 * Predicate defining frame conditions for brokerRecover action
 *
 * @recover_partitions : Partitions that were recovered
 */
pred brokerRecoverFrame[recover_partitions : TopicPartition] {
  -- Pre-existing replicas should preserve events
  all pre_existing_replicas : dom[events.KafkaEvent] | pre_existing_replicas.events' = pre_existing_replicas.events
  
  -- Partitions other than one's that needed recovery should preserve their follower replicas
  all other_p : dom[followers] - recover_partitions | other_p.followers' = other_p.followers

  -- Pre-existing brokers should preserve replicas
  all b : dom[replicasInBroker] | b.replicasInBroker' = b.replicasInBroker

  brokerRecoverUnaffectedVariablesFrame
}


/****************
 * MAIN MODEL
 ***************/

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
 * 1..3 steps. 208675 vars. 4514 primary vars. 611418 clauses. 7919ms.
 * Counterexample found. Assertion is invalid. 1509ms.
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
 * 1..3 steps. 276739 vars. 6140 primary vars. 802769 clauses. 542ms.
 * Counterexample found. Assertion is invalid. 93ms.
 */
assert SimpleKafkaPreservesInvariantsAfterCrash {
  kafkaSimpleBehavior[3] implies always(InvariantsAfterCrash[Kafka])
}
check SimpleKafkaPreservesInvariantsAfterCrash for 3


/**
 * kafkaFaultTolerantBehavior[3] ensures that a broker recovers after it crashes
 * Therefore, assertion holds because at least 2 replicas are always maintained
 *
 * RESULT: ------
 * Executing "Check FaultTolerantKafkaWithThreeReplicasPreservesInvariantsAfterCrash for 3"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=3 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..10 steps. 553375 vars. 12735 primary vars. 1683485 clauses. 51487ms.
 * No counterexample found. Assertion may be valid. 30632ms.
 * 
 * Executing "Check FaultTolerantKafkaWithThreeReplicasPreservesInvariantsAfterCrash for 4 but 9 steps"
 * Solver=sat4j Steps=1..9 Bitwidth=4 MaxSeq=4 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..9 steps. 917281 vars. 19242 primary vars. 2825093 clauses. 3327452ms.
 * No counterexample found. Assertion may be valid. 186673ms.

 * Executing "Check FaultTolerantKafkaWithThreeReplicasPreservesInvariantsAfterCrash for 3"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=3 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..10 steps. 553375 vars. 12735 primary vars. 1683485 clauses. 57519ms.
 * No counterexample found. Assertion may be valid. 18325ms.
 */
assert FaultTolerantKafkaWithThreeReplicasPreservesInvariantsAfterCrash {
  kafkaFaultTolerantBehavior[3] implies always(InvariantsAfterCrash[Kafka])
}
check FaultTolerantKafkaWithThreeReplicasPreservesInvariantsAfterCrash for 3


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
 */
assert FaultTolerantKafkaWithTwoReplicasPreservesInvariantsAfterCrash {
  kafkaFaultTolerantBehavior[2] implies always(InvariantsAfterCrash[Kafka])
}
check FaultTolerantKafkaWithTwoReplicasPreservesInvariantsAfterCrash for 4


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
 */
assert BrokerRecoverAfterCrashPreservesInvariantsStrict {
  kafkaFaultTolerantBehavior[3] implies always (
    -- After broker failure, InvariantsAfterCrash satisfies until broker recovers
    (executeBrokerCrash implies after(InvariantsAfterCrash[Kafka] until executeBrokerRecover))
    
    -- Strict invariants start to satisfy once a broker recovers
    and (executeBrokerRecover implies after(InvariantsStrict[Kafka]))
  )
}
check BrokerRecoverAfterCrashPreservesInvariantsStrict for 3


/**
 * If broker never goes down, Strict invariants satisfy for either of the two behaviors:
 * kafkaSimpleBehavior or kafkaFaultTolerantBehavior
 *
 * RESULT:
 * Executing "Check NeverBrokerCrashPreservesStrictInvariants for 3"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=3 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..10 steps. 554253 vars. 12735 primary vars. 1685883 clauses. 139380ms.
 * No counterexample found. Assertion may be valid. 7738ms.
 */
assert NeverBrokerCrashPreservesStrictInvariants {
  (kafkaSimpleBehavior[2] or kafkaFaultTolerantBehavior[2]) implies
    ((not eventually(executeBrokerCrash)) implies always(InvariantsStrict[Kafka]))
}
check NeverBrokerCrashPreservesStrictInvariants for 3


/**
 * LIVENESS: Everytime a broker crashes, it must recover at some point in the future
 * and must not crash again before that recovery
 *
 * RESULT: 
 * Executing "Check FaultTolerantKafkaEventuallyRecoversAfterCrash for 4"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=4 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..10 steps. 2413807 vars. 50805 primary vars. 7442066 clauses. 39830ms.
 * No counterexample found. Assertion may be valid. 372ms.
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
 * 1..10 steps. 371204 vars. 5900 primary vars. 1088532 clauses. 24650ms.
 * No counterexample found. Assertion may be valid. 2450ms.
 *
 * Executing "Check EventCanOnlyBeReadAfterBeingPushed for 3"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=3 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..10 steps. 3274378 vars. 63840 primary vars. 10079025 clauses. 103479ms.
 * No counterexample found. Assertion may be valid. 25209ms.
 */
assert EventCanOnlyBeReadAfterBeingPushed {
  -- Any behaviour with an initially empty cluster (without any events)
  (kafkaFaultTolerantBehavior[2] or kafkaSimpleBehavior[2]) and (no getAllEventsInCluster[Kafka]) implies (
    -- If an event was read, it should have been pushed in the past
    all p: TopicPartition, e: KafkaEvent | always ( eventReadFromPartition[e, p] implies once(eventPushedToPartition[e, p]) )
  )
}
check EventCanOnlyBeReadAfterBeingPushed for 3


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
check SequentialityWithinPartition for 3

/**
 * This asserts that an events in two different partitions can only be read in the order it was pushed in
 * This assertion is expected to result in a counterexample.
 *
 * Executing "Check SequentialityBetweenTwoPartitions for 4"
 * Solver=sat4j Steps=1..10 Bitwidth=4 MaxSeq=4 SkolemDepth=1 Symmetry=20 Mode=batch
 * 1..7 steps. 1207073 vars. 12726 primary vars. 3794187 clauses. 110647ms.
 * Counterexample found. Assertion is invalid. 12711ms.
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
check SequentialityBetweenTwoPartitions for 4

/******************************************************************************************************/
