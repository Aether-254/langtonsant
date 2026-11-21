import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0602 : checkSingleBlackFast (18, 14) 6230 .south (-14, -5) (-19, -16) = true := by
  decide +kernel

end LangtonsAnt
