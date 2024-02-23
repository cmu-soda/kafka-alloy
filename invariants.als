/***************
 * INVARIANTS
 ***************/

open signatures
open functions
open util/relation

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
