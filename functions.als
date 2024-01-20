/**********************
 * HELPER FUNCTIONS
 **********************/

open signatures

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
