import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0625 : checkSingleBlackFast (6, -9) 13724 .south (-14, -4) (-22, -22) = true := by
  decide +kernel

end LangtonsAnt
