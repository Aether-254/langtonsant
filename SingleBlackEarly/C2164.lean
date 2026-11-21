import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2164 : checkSingleBlackFast (-86, -68) 29915 .east (46, 34) (5, -56) = true := by
  decide +kernel

end LangtonsAnt
