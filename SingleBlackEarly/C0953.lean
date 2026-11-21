import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0953 : checkSingleBlackFast (7, 16) 11935 .east (-7, -1) (-20, -23) = true := by
  decide +kernel

end LangtonsAnt
