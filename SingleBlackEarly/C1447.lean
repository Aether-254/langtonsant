import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1447 : checkSingleBlackFast (-25, 3) 23860 .south (-3, -8) (-35, -4) = true := by
  decide +kernel

end LangtonsAnt
