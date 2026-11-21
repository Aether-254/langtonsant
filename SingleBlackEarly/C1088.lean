import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1088 : checkSingleBlackFast (-6, -8) 27666 .south (-3, 0) (-32, -17) = true := by
  decide +kernel

end LangtonsAnt
