import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2180 : checkSingleBlackFast (-91, -68) 21205 .east (43, 28) (20, -62) = true := by
  decide +kernel

end LangtonsAnt
