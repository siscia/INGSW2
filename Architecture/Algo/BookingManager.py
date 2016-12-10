class BookingManager():
    def __init__(self):
        self.reservation_running = min_heap()
        self.reservations = {}
        thread_expired = threading.Thread(target = self.manageExpired)
        thread_expired.start()

    def newBook(self, id_user, id_car):
        reservation = {"id_reservation" : newID(),
                       "id_car" : id_car,
                       "id_user" : id_user,
                       "expire_time" : time.now() + time.timedelta(hours = 1)}
        self.reservation_running.add((reservation["expire_time"], reservation))
        self.reservations[reservation["id_reservation"]] = reservation        
        return reservation["id_reservation"]

    def removeReservation(self, id_reservation):
        if id_reservation in self.reservations:
            reservation = self.reservations[id_reservation]
            self.reservation_running.remove(reservation)
            del self.reservation[id_reservation]
            return True
        return False

    def getReservation(self, id_reservation):
        return self.reservation[id_reservation]

    def manageExpired(self):
        while True:
            (expire_time, reservation) = self.reservation_running.pop()
            if expire_time > time.now():
                FineManager.expireReservation(reservation)
                self.removeReservation(reservation["id_reservation"])
            time.sleep(1)
