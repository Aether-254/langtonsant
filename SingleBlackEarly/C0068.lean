import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0068 : checkSingleBlackFast (-2, -5) 7112 .south (-14, -2) (-22, -2) = true := by
  decide +kernel

end LangtonsAnt
