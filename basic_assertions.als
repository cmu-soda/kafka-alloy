/*********************************************************************************************
 * BASIC ASSERTIONS
 * ---------------
 * This file contains assertions utilized to check if the object constraints and invariants
 * satisfy certain properties that must hold true throughout all valid instances of a Kafka
 * cluster.
 * Note: These assertions don't take any transition into account
 *********************************************************************************************/

open invariants
open signatures

/**************************************************
 * ALL ASSERTIONS HOLD:
 * 13 commands were executed. The results are:
 * #1: No counterexample found. EventsOfOneClusterShouldNotBePresentInAnExternalBroker may be valid.
 * #2: No counterexample found. TopicPartitionMustHaveOneLeader may be valid.
 * #3: No counterexample found. NumPartitionsReplicasCannotExceedNumBrokers may be valid.
 * #4: No counterexample found. AllEventsInClusterShouldBePresentInBrokers may be valid.
 * #5: No counterexample found. ParitionsOfSubscribedTopicsMustHaveOneOffset may be valid.
 * #6: No counterexample found. ConsumerMustBeAssignedOnlyToPartitionsOfGroupSubscribedTopics may be valid.
 * #7: No counterexample found. ConsumerGroupShouldContainAssignmentData may be valid.
 * #8: No counterexample found. EveryPartitionOfSubscribedTopicMustBeAssignedToAConsumer may be valid.
 * #9: No counterexample found. PartitionAssignedToOneConsumerInGroup may be valid.
 * #10: No counterexample found. NoConsumerIdle may be valid.
 * #11: No counterexample found. ReplicasMustBeUnshared may be valid.
 * #12: No counterexample found. EventsCannotBelongToTwoPartitions may be valid.
 * #13: No counterexample found. ClusterConsumerBelongsToClusterCG may be valid.
 */

/**
 * Events should not be exposed to servers outside the kafka cluster it belongs to
 */
assert EventsOfOneClusterShouldNotBePresentInAnExternalBroker {
  all k : Kafka | InvariantsStrict[k] implies (
    all e : k.zookeeper.topics.partitions.(leader+followers).events.elems |
      (events.e.Int).~replicasInBroker in k.zookeeper.brokers
  )
}
check EventsOfOneClusterShouldNotBePresentInAnExternalBroker for 5


/**
 * Each partition should always have exactly one leader replica
 */
assert TopicPartitionMustHaveOneLeader {
  all k: Kafka, p : k.zookeeper.topics.partitions | InvariantsStrict[k] implies one p.leader
}
check TopicPartitionMustHaveOneLeader for 5

/**
 * Number of replicas per partition cannot be more than the number of brokers
 * in the cluster
 */
assert NumPartitionsReplicasCannotExceedNumBrokers {
  all k : Kafka, p: k.zookeeper.topics.partitions | 
    InvariantsStrict[k] implies #getPartitionReplicas[p] <= #k.zookeeper.brokers
}
check NumPartitionsReplicasCannotExceedNumBrokers for 5

/**
 * Events present in each topic of the cluster must be present in its Brokers
 */
assert AllEventsInClusterShouldBePresentInBrokers {
  all k : Kafka | InvariantsStrict[k] implies
    getAllEventsInCluster[k] = k.zookeeper.brokers.replicasInBroker.events.elems
}
check AllEventsInClusterShouldBePresentInBrokers for 5


/**
 * ConsumerGroup should have exactly one offset value corresponding to each partition
 * of topics that the ConsumerGroup subscribes to
 */
assert ParitionsOfSubscribedTopicsMustHaveOneOffset {
  all cg:ConsumerGroup , p : cg.subscribedTo.partitions | one cg.offsets[p]
}
check ParitionsOfSubscribedTopicsMustHaveOneOffset for 5


/**
 * Consumers must be assigned to parititions of topics that its consumer group is subscribed to
 */
assert ConsumerMustBeAssignedOnlyToPartitionsOfGroupSubscribedTopics {
  all cg:ConsumerGroup | cg.consumers.assignedTo in cg.subscribedTo.partitions
}
check ConsumerMustBeAssignedOnlyToPartitionsOfGroupSubscribedTopics for 5

/**
 * Metadata about partitions assigned to consumer should be present in its ConsumerGroup
 *
 * Consumer Group should contain consumer assignment data only about 
 * consumers belonging to the group
 */
assert ConsumerGroupShouldContainAssignmentData {
  all cg : ConsumerGroup | dom[cg.assignments] = cg.consumers
}
check ConsumerGroupShouldContainAssignmentData for 5


/**
 * Each partition of topics subscribed by a ConsumerGroup should be assigned to a consumer
 * belonging to the group
 */
assert EveryPartitionOfSubscribedTopicMustBeAssignedToAConsumer{
  all cg:ConsumerGroup  | cg.subscribedTo.partitions in ran[cg.assignments]
}
check EveryPartitionOfSubscribedTopicMustBeAssignedToAConsumer for 5


/**
 * A partition cannot be shared between two consumers within a consumer group
 */
assert PartitionAssignedToOneConsumerInGroup {
  always (all cg:ConsumerGroup | all disj c1, c2 : cg.consumers | 
    disj[c1.assignedTo, c2.assignedTo])
}
check PartitionAssignedToOneConsumerInGroup for 5


/**
 * No Consumer in a ConsumerGroup should be unassigned to a Partition
 */
assert NoConsumerIdle {
  all cg:ConsumerGroup | all c : cg.consumers |   some c.assignedTo
}
check NoConsumerIdle for 5


/**
 * No replica can be shared between two Partitions
 * This assertion specifically ensures that a leader of one partition cannot be a follower of
 * another partition, and vice versa.
 */
assert ReplicasMustBeUnshared {
  all p : TopicPartition | 
      disj[p.(leader + followers), (TopicPartition - p).(leader + followers)]
}
check ReplicasMustBeUnshared for 5


/**
 * Events of one partition cannot belong to another partition
 */
assert EventsCannotBelongToTwoPartitions {
  all k : Kafka, p : k.zookeeper.topics.partitions | 
    disj[p.leader.events.elems, (TopicPartition - p).leader.events.elems]
}
check EventsCannotBelongToTwoPartitions for 5

/**
 * Consumers of ConsumerGroup of the cluster must not belong to any other consumer group
 */
assert ClusterConsumerBelongsToClusterCG {
  all k : Kafka, c : k.consumer_groups.consumers | c.~consumers in k.consumer_groups
}
check ClusterConsumerBelongsToClusterCG for 5
