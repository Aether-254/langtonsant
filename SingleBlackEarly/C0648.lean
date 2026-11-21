import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0648 : checkSingleBlackFast (9, -10) 5169 .west (-7, 4) (-18, -8) = true := by
  decide +kernel

end LangtonsAnt
