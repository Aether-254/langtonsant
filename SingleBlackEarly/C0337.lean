import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0337 : checkSingleBlackFast (3, 14) 7188 .south (-9, -4) (-19, -14) = true := by
  decide +kernel

end LangtonsAnt
