sig Individual {
    position: one Place  // Every individual has exactly one position
}

sig Resource {
    position: one Place  // Every resource has exactly one position
}

abstract sig Place {}

sig Residence extends Place {}   
sig Storage extends Place {}     
sig JobSite extends Place {
    neededWorkers: Int,          // Number of workers required to complete work
    neededResources: set Resource // Resources required to complete work
}

abstract sig Transport {
    currentPosition: one Place  // Each transport has a position
}

// Personal transports with maxCapacity constraint
sig PersonalTransport extends Transport {
    seatLimit: Int,
    occupants: set Individual
} {
    #occupants <= seatLimit
}

// Freight transports with maxLoad constraint
sig FreightTransport extends Transport {
    loadLimit: Int,
    load: set Resource
} {
    #load <= loadLimit
}

// Move someone using transport
pred relocateIndividual[ind: Individual, from: Place, to: Place, t: PersonalTransport] {
    ind.position = from
    ind.position' = to
    t.currentPosition = from
    t.currentPosition' = to
    #t.occupants < t.seatLimit
    t.occupants' = t.occupants + ind
}

// Move resources using a freight transport
pred relocateResource[r: Resource, from: Place, to: Place, t: FreightTransport] {
    r.position = from
    r.position' = to
    t.currentPosition = from
    t.currentPosition' = to
    #t.load < t.loadLimit  
    t.load' = t.load + r  
}

// Check if a job site has enough workers and resources to complete a task
pred finishTask[j: JobSite] {
    # { i: Individual | i.position = j } >= j.neededWorkers
    j.neededResources in { r: Resource | r.position = j }
    
    no j'
}

// Ensure job sites have necessary resources
fact JobRequirements {
    all j: JobSite | 
        (# { i: Individual | i.position = j } >= j.neededWorkers) and
        (j.neededResources in { r: Resource | r.position = j })
}

// Make sure individuals are in transport, storage, a residence, or job site
fact ValidIndividualPosition {
    all i: Individual | i.position in (Residence + Storage + JobSite + Transport)
}

// Ensure resources are stored in storage facilities or at freight transport
fact ValidResourcePosition {
    all r: Resource | r.position in (Storage + FreightTransport)
}

run {} for 15
