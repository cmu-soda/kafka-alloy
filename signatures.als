/***************
 * SIGNATURES
 ***************/

open util/relation

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