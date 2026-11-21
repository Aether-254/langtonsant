import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1308 : checkSingleBlackFast (-9, 16) 25432 .south (-8, -12) (-34, -4) = true := by
  decide +kernel

end LangtonsAnt
