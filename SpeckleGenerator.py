"""
SpeckleGenerator.py

Transcribed verbatim from the generator documented in the Speckle.v header
comment (which itself quotes the original email):

    def speckle_pattern(n, m, k):
        szX = int(n/k); szY = int(m/k)
        fourier_spectrum = np.exp(1j*2*np.pi*np.random.rand(szY,szX))
        fspace_full = np.zeros((m,n), dtype=complex)
        fspace_full[0:szY,0:szX] += fourier_spectrum
        specklefield = fft2(fspace_full)
        speckelIntensity = np.abs(specklefield)**2
        return speckelIntensity

    def speckle_image(n, m, k):
        speckle = speckle_pattern(n, m, k)
        scale = 1/(speckle.max()/255)
        grayscale = (scale*speckle).astype(np.uint8)
        return Image.fromarray(grayscale)

Index convention (per Speckle.v): x is the column (0..n-1), y is the row
(0..m-1); fspace_full has numpy shape (m, n) = (rows, cols).  numpy's forward
fft2 uses the exp(-2*pi*i*...) sign convention, matching Speckle.v's dft.
astype(uint8) truncates toward zero == floor for nonnegative reals, matching
Num.floor in Speckle.v.
"""

import numpy as np
from numpy.fft import fft2
from PIL import Image


def speckle_pattern(n, m, k):
    szX = int(n / k)
    szY = int(m / k)
    fourier_spectrum = np.exp(1j * 2 * np.pi * np.random.rand(szY, szX))
    fspace_full = np.zeros((m, n), dtype=complex)
    fspace_full[0:szY, 0:szX] += fourier_spectrum
    specklefield = fft2(fspace_full)
    speckle_intensity = np.abs(specklefield) ** 2
    return speckle_intensity


def speckle_image_np(n, m, k):
    """Return the uint8 grayscale numpy array (shape (m, n))."""
    speckle = speckle_pattern(n, m, k)
    scale = 1 / (speckle.max() / 255)
    grayscale = (scale * speckle).astype(np.uint8)
    return grayscale


def speckle_image(n, m, k):
    """Return a PIL Image, exactly as in the comment."""
    return Image.fromarray(speckle_image_np(n, m, k))


def write_txt(arr, path):
    """Write the array in the plain-text format the OCaml driver reads:
    'w h' on line 1, then w*h values row-major (y outer, x inner)."""
    m, n = arr.shape  # rows=m=height, cols=n=width
    with open(path, "w") as f:
        f.write("{} {}\n".format(n, m))  # w h
        flat = arr.reshape(-1)  # C-order: y outer, x inner
        f.write(" ".join(str(int(v)) for v in flat))
        f.write("\n")


if __name__ == "__main__":
    import os
    import sys

    # configuration (kept small so the extracted Coq model runs quickly)
    N = 48          # width  (n, x)
    M = 48          # height (m, y)
    K = 6           # correlation length -> szX=szY=8 (64 phasors)
    COUNT = 10
    SEED = 20260612

    out_dir = sys.argv[1] if len(sys.argv) > 1 else "images"
    os.makedirs(out_dir, exist_ok=True)

    np.random.seed(SEED)
    manifest = []
    for i in range(COUNT):
        arr = speckle_image_np(N, M, K)
        txt = os.path.join(out_dir, "img_{:02d}.txt".format(i))
        npy = os.path.join(out_dir, "img_{:02d}.npy".format(i))
        write_txt(arr, txt)
        np.save(npy, arr)
        manifest.append((i, txt, npy))
        print("img_{:02d}: shape={} max={} min={} nonzero={}".format(
            i, arr.shape, int(arr.max()), int(arr.min()), int(np.count_nonzero(arr))))

    print("wrote {} images ({}x{}, k={}) to {}".format(COUNT, N, M, K, out_dir))
