#RASD

Simone Mosciatti & Sara Zanzottera

#HSLIDE

Anticipation of some design choice.
* Client Server architecture
* Yes we are aware we shouldn't
* It makes easier to explain

#VSLIDE



#HSLIDE

## Fundamental assumptions

* The system is able to prevent the ignition of each car’s engine remotely.
* The system is able to switch off every car’s engine remotely.
* The system is able to unlock each car remotely.
* The total running time of an ride is counted from either when the user switches the engine on or after 3 minutes from the unlock.
* The total running time of an ride ends when the user locks the car.

#VSLIDE

![Change of statuses](UML/StateDiagramCarAvailability.png)

## Statuses of the cars

* Availability
* Charging Status
* Exception Status

#HSLIDE

## External Services

* Payment processor
* Car position 
* License information
* Cars maintenance

#HSSLIDE

## Domain Proporties

* Personal account
* Staff can move the car
* Count of passengers

#HSLIDE

## Goals I

* REGISTRATION: Users can register to PowerEnJoy.
* LOGIN: Users can login to PowerEnJoy.
* LOOKUP: Users can find cars nearby a given position, it could be its position or a point in the map.
* BOOK: Users can book a car for a short amount of time.
* UNLOCK: When users are in proximity of the car they booked, the system can unlock it.

#VSLIDE

## Goals II

* RIDE: Users can drive to their destination.
* SAFE: AREAS Users can locate safe parking areas.
* UNSAFE: PARKING The system must react to an unsafe parking.
* POWER: STATIONS Users can locate charging stations.
* CHARGE: At the end of the ride, users are charged a fee.

#VSLIDE

## Goals III

* PAYMENTS: Users can pay bills through the app.
* FIND ISSUES: The staff can locate cars that need their intervention.
* SUPPORT: The staff can identify and solve car’s issues.
* FINES: The system can manage fines sent to the company by local authorities.

#HSLIDE

## Non functional requirement

* Latency: 99% of request should receive an answer in less than 300ms
* Availability: 99%
* Reliability: 99%

Trade a couple of nines for faster development cycle and smaller cost.

#HSLIDE

# Alloy

![Alloy class diagram](UML/ClassDiagram.png)

#VSLIDE	

## Static Alloy

### Verify absence of impossible situation

A lot of small model.

Easy to check and to verify each small module.

Merge into a bigger models, make sure that nothing can go wrong with different part interating

#VSLIDE

## Dynamic Alloy

### Verify correctness also of interation between users and cars

Another small dynamic model.

User interacting with the cars.


