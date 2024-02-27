open signatures
open functions
open util/relation

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
