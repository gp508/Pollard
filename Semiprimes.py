from math import floor,sqrt
import random

def isPrime(n):
    if(n<2):
        return False
    for i in range (2,floor(sqrt(n))+1):
        if n % i == 0:
            return False
    return True

def getRandomPrime(max):
    prime = 1
    while (not isPrime(prime)):
        prime = random.randint(2,max)
    return prime

def getRandomSemiprime(max):
    return getRandomPrime(max) * getRandomPrime(max)

for i in range(100):
    print(getRandomSemiprime(10000))