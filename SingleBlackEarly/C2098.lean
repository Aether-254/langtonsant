import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2098 : checkSingleBlackFast (-80, -62) 29603 .east (43, 31) (2, -53) = true := by
  decide +kernel

end LangtonsAnt
