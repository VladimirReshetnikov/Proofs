# Verify: at hole point j=-r (r>0), k=(n-2r+1)/2, with n odd, r odd, r>=3, r<=n, r%4==n%4:
#   D=(n+j)/2-k, M=n-k satisfy M=k+4D+1 and (k+D) even (Hole's hypothesis).
for n in range(1,80,2):          # n odd
  for r in range(3, n+1, 2):     # r odd, 3<=r<=n
    if r % 4 != n % 4: continue
    if 2*r-1 > n: continue
    if (n-2*r+1) % 2 != 0: continue
    k=(n-2*r+1)//2
    if k < 0: continue
    j=-r
    if (n+j) % 2 != 0: continue
    D=(n+j)//2 - k
    M=n-k
    assert M == k+4*D+1, (n,r,k,D,M)
    assert (k+D)%2==0, (n,r,k,D,M,"parity")
    assert D>=1, (n,r,D)
print("all hole points map to Hole hypothesis (k+D even, M=k+4D+1, D>=1): OK")
