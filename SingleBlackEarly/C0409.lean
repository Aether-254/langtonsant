import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0409 : checkSingleBlackFast (16, -5) 8532 .south (-7, -4) (-21, -14) = true := by
  decide +kernel

end LangtonsAnt
