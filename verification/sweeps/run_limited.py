"""Hard wall-clock timeout and Windows job memory cap for each independent run."""
if not __debug__:
    raise SystemExit("Verification requires assertions; run without -O/-OO or PYTHONOPTIMIZE.")
import ctypes, os, subprocess, sys, time
from ctypes import wintypes
class BASIC(ctypes.Structure):
    _fields_=[('ProcessTime',ctypes.c_int64),('JobTime',ctypes.c_int64),('Flags',wintypes.DWORD),('MinWS',ctypes.c_size_t),('MaxWS',ctypes.c_size_t),('Active',wintypes.DWORD),('Affinity',ctypes.c_size_t),('Priority',wintypes.DWORD),('Scheduling',wintypes.DWORD)]
class IO(ctypes.Structure):
    _fields_=[(s,ctypes.c_uint64) for s in ['ReadOps','WriteOps','OtherOps','ReadBytes','WriteBytes','OtherBytes']]
class EXT(ctypes.Structure):
    _fields_=[('Basic',BASIC),('IO',IO),('ProcessMem',ctypes.c_size_t),('JobMem',ctypes.c_size_t),('PeakProcess',ctypes.c_size_t),('PeakJob',ctypes.c_size_t)]
k=ctypes.WinDLL('kernel32',use_last_error=True)
k.CreateJobObjectW.restype=wintypes.HANDLE
k.SetInformationJobObject.argtypes=[wintypes.HANDLE,ctypes.c_int,ctypes.c_void_p,wintypes.DWORD]
k.AssignProcessToJobObject.argtypes=[wintypes.HANDLE,wintypes.HANDLE]
k.TerminateJobObject.argtypes=[wintypes.HANDLE,wintypes.UINT]
job=k.CreateJobObjectW(None,None)
limits=EXT(); limits.Basic.Flags=0x100|0x2000; limits.ProcessMem=1024**3
assert k.SetInformationJobObject(job,9,ctypes.byref(limits),ctypes.sizeof(limits)),ctypes.get_last_error()
env=os.environ.copy()
for name in ['OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:
    env[name]='1'
env['PYTHONDONTWRITEBYTECODE']='1'
seconds=int(sys.argv[1]); start=time.monotonic()
p=subprocess.Popen([sys.executable,'-u','-B']+sys.argv[2:],env=env)
assert k.AssignProcessToJobObject(job,wintypes.HANDLE(p._handle)),ctypes.get_last_error()
try:
    rc=p.wait(timeout=seconds)
except subprocess.TimeoutExpired:
    k.TerminateJobObject(job,124); p.wait(); rc=124
print('RUN_EXIT',rc,'wall_seconds',round(time.monotonic()-start,3),'memory_cap_bytes',limits.ProcessMem,flush=True)
sys.exit(rc)
