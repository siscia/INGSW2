#RASD

Simone Mosciatti & Sara Zanzottera

#HSLIDE

Anticipation of some design choice.
* Client Server architecture
* Yes we are aware we shouldn't
* It makes easier to explain

#HSLIDE

![Use Case Diagram](UML/UseCaseDiagram.png)

#HSLIDE

## Goals

* REGISTRATION Users can register to PowerEnJoy.
* LOGIN Users can login to PowerEnJoy.
* LOOKUP Users can find cars nearby a given position, it could be its position or a point in the map.
* BOOK Users can book a car for a short amount of time.
* UNLOCK When users are in proximity of the car they booked, the system can unlock
* it.
* RIDE Users can drive to their destination.
* SAFE AREAS Users can locate safe parking areas.
* UNSAFE PARKING The system must react to an unsafe parking.
* POWER STATIONS Users can locate charging stations.
* CHARGE At the end of the ride, users are charged a fee.
* PAYMENTS Users can pay bills through the app.
* FIND ISSUES The staff can locate cars that need their intervention.
* SUPPORT The staff can identify and solve car’s issues.
* FINES The system can manage fines sent to the company by local authorities.

#HSLIDE

# Alloy

![Alloy class diagram](UML/ClassDiagram.png)

#VSLIDE	

## Static Alloy

### Verify absence of impossible situation

A lot of small model.

Easy to check and to verify each small module.

Merge into a bigger models, make sure that nothing can go wrong with different part iterating

#VSLIDE

## Dynamic Alloy

### Verify correctness also of iteration

Another small dynamic model.

User interacting with the cars.


