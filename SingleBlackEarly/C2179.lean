import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2179 : checkSingleBlackFast (-90, -68) 20483 .east (35, 29) (2, -47) = true := by
  decide +kernel

end LangtonsAnt
