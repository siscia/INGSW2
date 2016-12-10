

class BookingManager():
    def __init__(self):
        self.prenotation_running = min_heap()
        self.prenotations = {}
        thread_expired = threading.Thread(target = self.manageExpired)
        thread_expired.start()

    def newBook(self, id_user, id_car):
        prenotation = {"id_prenotation" : newID(),
                       "id_car" : id_car,
                       "id_user" : id_user,
                       "expire_time" : time.now() + time.timedelta(hours = 1)}
        self.prenotation_running.add((prenotation["expire_time"], prenotation))
        self.prenotations[prenotation["id_prenotation"]] = prenotation        
        return prenotation["id_prenotation"]

    def removePrenotation(self, id_prenotation):
        if id_prenotation in self.prenotations:
            prenotation = self.prenotations[id_prenotation]
            self.prenotation_running.remove(prenotation)
            del self.prenotation[id_prenotation]
            return True
        return False

    def getPrenotation(self, id_prenotation):
        return self.prenotation[id_prenotation]

    def manageExpired(self):
        while True:
            (expire_time, prenotation) = self.prenotation_running.pop()
            if expire_time > time.now():
                FineManager.expirePrenotation(prenotation)
                self.removePrenotation(prenotation["id_prenotation"])
            time.sleep(1)
            
